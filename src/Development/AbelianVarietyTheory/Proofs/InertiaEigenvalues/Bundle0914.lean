module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsAllEmbeddingsOfInclusionReading
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0782
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0738
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0908
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0909
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0779
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnisotropicTermsMeanZeroUnipotentRadical
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0451
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepRealPointFockVectorSubstitution
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0792
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0963
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunction
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0911

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanLe
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CuspDescent

theorem exists_indep_comb {K R V : Type} [Field K] [AddCommGroup R] [Module K R] [AddCommGroup V] [Module ℂ V]
    (σ : K →+* ℂ) (ρ : R →ₛₗ[σ] V) (S : Submodule K R) {P : V} (hP : P ∈ Submodule.span ℂ (ρ '' (S : Set R))) :
    ∃ (m : ℕ) (e : Fin m → ℂ) (f : Fin m → R), (∀ i, f i ∈ S) ∧
      (∀ c : Fin m → K, ∑ i, σ (c i) * e i = 0 → c = 0) ∧ P = ∑ i, e i • ρ (f i) := by
  obtain ⟨n, z, v, hv⟩ := Submodule.mem_span_set'.1 hP
  choose g hg hgv using fun k => (v k).2
  letI : Algebra K ℂ := σ.toAlgebra
  have hsm : ∀ (a : K) (x : ℂ), a • x = σ a * x := fun a x => by rw [Algebra.smul_def]; rfl
  let W : Submodule K ℂ := Submodule.span K (Set.range z)
  have hzW : ∀ k, z k ∈ W := fun k => Submodule.subset_span ⟨k, rfl⟩
  haveI : FiniteDimensional K W := FiniteDimensional.span_of_finite K (Set.finite_range z)
  let ζ := Module.finBasis K W
  let β : Fin n → Fin (Module.finrank K W) → K := fun k m => ζ.repr ⟨z k, hzW k⟩ m
  have hzexp : ∀ k, z k = ∑ m, σ (β k m) * (ζ m : ℂ) := by
    intro k
    have h2 := congrArg Subtype.val (ζ.sum_repr ⟨z k, hzW k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hsm] at h2
    exact h2.symm
  have hlin : LinearIndependent K (fun m => (ζ m : ℂ)) :=
    ζ.linearIndependent.map' W.subtype (Submodule.ker_subtype _)
  refine ⟨_, fun m => (ζ m : ℂ), fun m => ∑ k, β k m • g k,
    fun m => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k), fun c hc => ?_, ?_⟩
  · funext m
    exact (Fintype.linearIndependent_iff.1 hlin) c (by simpa only [hsm] using hc) m
  · rw [← hv]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, Finset.smul_sum, smul_smul, hgv]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_smul, hzexp k]
    congr 1
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _

section Geometric

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem rd_prod {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (N : ℕ) (f : Fin (N + 1) → Rul Xo c) :
    rdU U (∏ t, f t) = ∏ t, rdU U (f t) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Fin.prod_univ_castSucc, GlobalTheory.CuspAllEmb.rd_mul, ih, ← Fin.prod_univ_castSucc fun t => rdU U (f t)]

theorem prod_mem_sec {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (N : ℕ) (f : Fin (N + 1) → Rul Xo c)
    (hf : ∀ t, f t ∈ sec Xo c a n) : ∏ t, f t ∈ sec Xo c ((N + 1) • a) ((N + 1) * n) := by
  induction N with
  | zero => simpa using hf 0
  | succ N ih =>
    rw [succ_nsmul, add_mul _ 1, one_mul, Fin.prod_univ_castSucc]
    exact sec_mul Xo c _ _ _ _ (ih _ fun t => hf _) (hf _)

theorem pow_comb {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (N : ℕ) {ι : Type} [Fintype ι] (e : ι → ℂ) (f : ι → Rul Xo c) :
    (∑ i, e i • rdU U (f i)) ^ (N + 1) =
      ∑ p : Fin (N + 1) → ι, (∏ t, e (p t)) • rdU U (∏ t, f (p t)) := by
  classical
  rw [Fintype.sum_pow]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [rd_prod, Finset.prod_smul]

theorem isSec_comb (X : Data E r) (la : Wt X.Ψ r) {ι : Type} [Fintype ι] (e : ι → ℂ) (Q : ι → Frame X.Ψ r → ℂ)
    (hQ : ∀ i, X.IsSec la (Q i)) : X.IsSec la (∑ i, e i • Q i) := by
  refine ⟨DifferentiableOn.sum fun i _ => (hQ i).1.const_smul (e i), fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [(hQ i).2.1 x hx b hb]; ring
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [(hQ i).2.2 γ hγ x hx]; ring

theorem descent (hf : 1 < Module.finrank ℚ E / 2) {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hU : IsUnf U)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n) (N : ℕ)
    (hI : ∀ (m : ℕ) (b : Fin m → Rul Xo c), (∀ i, b i ∈ sec Xo c ((N + 1) • a) ((N + 1) * n)) →
      LinearIndependent c.F b → LinearIndependent ℂ fun i => rdU U (b i))
    (hspan : holSub0 U.X (laU U ((N + 1) • a) ((N + 1) * n)) ≤ Submodule.span ℂ (rdU U ''
      {g | g ∈ sec Xo c ((N + 1) • a) ((N + 1) * n) ∧ rdU U g ∈ holSub0 U.X (laU U ((N + 1) • a) ((N + 1) * n))})) :
    holSub0 U.X (laU U a n) ⊓ Submodule.span ℂ (rdU U '' (sec Xo c a n : Set (Rul Xo c))) ≤
      Submodule.span ℂ (rdU U '' {f | f ∈ sec Xo c a n ∧ rdU U f ∈ holSub0 U.X (laU U a n)}) := by
  classical
  rintro P ⟨hP, hPs⟩
  obtain ⟨m, e, f, hfs, he, rfl⟩ := exists_indep_comb σ (rdU U) _ hPs
  have hoff : ∀ e' : Fin m → ℂ, ∑ i, e' i • rdU U (f i) ∈ offZero U.X := fun e' =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (rdU_mem_offZero _ _)
  have hpow : (∑ i, e i • rdU U (f i)) ^ (N + 1) ∈ holSub0 U.X (laU U ((N + 1) • a) ((N + 1) * n)) := by
    refine ⟨(GlobalTheory.CuspAllEmb.mem_holSub _ _ _).2 fun k => ?_, ?_⟩
    · have h1 := (GlobalTheory.CuspAllEmb.mem_holSub _ _ _).1 hP.1 k
      rw [GlobalTheory.CuspAllEmb.la_smul _ _ hd.2]
      rcases N with _ | N
      · simpa using h1
      · have h2 := GlobalTheory.CuspAllEmb.ss_mul _ hf h1 (GlobalTheory.CuspAllEmb.isSec_pow _ h1.1.1 N)
        rw [← pow_succ', ← succ_nsmul'] at h2
        exact h2
    · rw [pow_comb]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (rdU_mem_offZero _ _)
  obtain ⟨q, z, v, hv⟩ := Submodule.mem_span_set'.1 (hspan hpow)
  choose g hg hgv using fun k => (v k).2
  have conj : ∀ φ : ℂ ≃+* ℂ, (∀ x, φ (σ x) = σ x) →
      ∑ i, φ (e i) • rdU U (f i) ∈ holSub0 U.X (laU U a n) := by
    intro φ hφ
    have tr := GlobalTheory.CuspAllEmb.transfer (φ : ℂ →+* ℂ) hφ (rdU U) (rdU U) _ hI
      (fun p : Fin (N + 1) → Fin m => ∏ t, f (p t)) g (fun p => prod_mem_sec N _ fun t => hfs _) (fun k => (hg k).1)
      (fun p => ∏ t, e (p t)) z (by rw [← pow_comb, ← hv]; simp only [hgv])
    simp only [map_prod, RingHom.coe_coe] at tr
    rw [← pow_comb U N (fun i => φ (e i)) f] at tr
    have hm : (∑ i, φ (e i) • rdU U (f i)) ^ (N + 1) ∈ holSub0 U.X (laU U ((N + 1) • a) ((N + 1) * n)) := by
      rw [tr]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k).2
    refine ⟨(GlobalTheory.CuspAllEmb.mem_holSub _ _ _).2 fun k => ?_, hoff _⟩
    have h1 := (GlobalTheory.CuspAllEmb.mem_holSub _ _ _).1 hm.1 k
    rw [GlobalTheory.CuspAllEmb.la_smul _ _ hd.2] at h1
    refine GlobalTheory.CuspAllEmb.ss_of_pow _ hf ?_ N h1
    have := isSec_comb (U.X k) (laU U a n k) (fun i => φ (e i)) (fun i => rdU U (f i) k)
      (fun i => hU.2.2.2.2.1 a n hd _ (hfs i) k)
    simpa only [Finset.sum_apply, Pi.smul_apply] using this
  haveI := c.fin
  haveI : NumberField c.F := {}
  have htop := _root_.GlobalTheory.ConjSpan.span_conj_eq_top c.F σ (Fin m) e he
  let L : (Fin m → ℂ) →ₗ[ℂ] FDSec U.X := Fintype.linearCombination ℂ fun i => rdU U (f i)
  have hle : (⊤ : Submodule ℂ (Fin m → ℂ)) ≤ (holSub0 U.X (laU U a n)).comap L := by
    rw [← htop, Submodule.span_le]
    rintro _ ⟨φ, hφ, rfl⟩
    exact conj φ hφ
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨f i, ⟨hfs i, ?_⟩, rfl⟩)
  have := hle (Submodule.mem_top (x := Pi.single i 1))
  simpa [L] using this

end Geometric


attribute [local instance] Formalism.BasicNotions.Host.cmStar in
set_option maxHeartbeats 1000000 in
theorem cusp_descends : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ w : WeightFamilies.Wt D j, w.LastPos → 0 < w.n → holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) ⊓ Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c (wtA w) w.n : Set (Rul (T.Q.Xo j) T.Q.c))) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) (wtA w) w.n)}) := by
  intro D T h j hj σ hσ w hw hn
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := Formalism.L2.Pj.hostSize_finrank D
  have h8 := D.eight_le_f
  set N := 8 * D.R.f * D.R.r + 3 with hN
  have hA : wtA (WeightAlgebra.wsmul (N + 1) w) = (N + 1) • wtA w := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    unfold wtA
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [WeightAlgebra.wsmul, ext0]
    split_ifs <;> ring
  have hd : Dom ((N + 1) • wtA w) ((N + 1) * w.n) := hA ▸ dom_wtA (WeightAlgebra.wsmul (N + 1) w)
  refine descent (by omega) (T.U j σ) (h.unf j hj σ hσ) (dom_wtA w) N
    (GlobalTheory.rdIndep_of_lawsM D T.toCore h.toLawsM j hj σ hσ _ _ hd) ?_
  have key := GlobalTheory.OntoCore.holSub0_le_span_cuspA D T h j hj (WeightAlgebra.wsmul (N + 1) w)
    (fun τ i hi => Nat.mul_pos (Nat.succ_pos N) (hw τ i hi)) (Nat.le_mul_of_pos_right _ hn) σ hσ
  rw [hA] at key
  refine key.trans (Submodule.span_mono (Set.image_mono fun g hg => ?_))
  exact ⟨cusp_le_sec _ _ _ _ _ hg, ((mem_cusp _ _ _ _ _ _).1 hg).2 σ hσ, rdU_mem_offZero _ _⟩

end GlobalTheory.CuspDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsThetaFunctionOfMemSpanVacuumTranslates
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem isThetaFunO_of_mem_trSp : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (e : AE D) (M : ℕ) (O : Subring ℂ), ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, IsThetaFunO ψ V W f := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP e M O f hf
  have hψ : IsStdChar D ψ (-1) := hP.1.weil.std
  have h0 : IsThetaFunO ψ V W f₀ := GlobalTheory.OneMapRef.isThetaFunO_of_isVacO hP.2.2.2.2.2.2.2.2
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, -, -, rfl⟩ := hx
    exact GlobalTheory.AnisoMean.isTheta_heisO hψ h0 y
  | zero => exact GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ V W
  | add x y _ _ hx hy => exact GlobalTheory.LocMod.LinSpace.isThetaFunO_add hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def]
    exact GlobalTheory.LocMod.LinSpace.isThetaFunO_smul (a : ℂ) hx

end GlobalTheory.LevelSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealRationalPointActsHarmonicSubstitution
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries.ArchAct

theorem det_pow_mem {n : ℕ} (O : Subring ℂ) (z : ℂ) (g : GL (Fin n) ℂ)
    (h1 : ∀ x y, z * (g : Matrix (Fin n) (Fin n) ℂ) x y ∈ O)
    (h2 : ∀ x y, z * ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) x y ∈ O) (k : ℤ) :
    z ^ (n * k.natAbs) * (g : Matrix (Fin n) (Fin n) ℂ).det ^ k ∈ O := by
  have hdet : ∀ A : Matrix (Fin n) (Fin n) ℂ, (∀ x y, z * A x y ∈ O) → z ^ n * A.det ∈ O := by
    intro A hA
    have e : z ^ n * A.det = (z • A).det := by rw [Matrix.det_smul, Fintype.card_fin]
    rw [e, Matrix.det_apply]
    refine Subring.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    refine zsmul_mem (Subring.prod_mem _ fun i _ => ?_) _
    simpa [Matrix.smul_apply] using hA (σ i) i
  have hinv : ((g : Matrix (Fin n) (Fin n) ℂ).det)⁻¹ = ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det := by
    rw [eq_comm]
    apply eq_inv_of_mul_eq_one_left
    rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
  obtain ⟨k, rfl | rfl⟩ := k.eq_nat_or_neg
  · rw [Int.natAbs_natCast, zpow_natCast, pow_mul, ← mul_pow]
    exact pow_mem (hdet _ h1) _
  · rw [Int.natAbs_neg, Int.natAbs_natCast, _root_.zpow_neg, zpow_natCast, ← inv_pow, hinv, pow_mul, ← mul_pow]
    exact pow_mem (hdet _ h2) _

theorem real_act_harm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (lt : LtN Dw V.rank ≃ FVar D W.rank V.rank) (wa : (D.host.E →+* ℂ) × ℕ → ℕ), W.rank = Dw.p + Dw.q → (∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) → (∀ τ, IsONBasis (gramAt D W τ) (sW τ) (BW τ) Dw.p) → IsLetters Dw lt → ∀ l c : ℕ, ∃ c' : ℕ, ∀ (γ a : GA D V) (γ' : GL (Fin V.rank) D.host.E) (O : Subring ℂ), γ ∈ GQ V → GlobalTheory.Member.IsRat V γ γ' → a ∈ GinfC V → γ * a ∈ GfC V → (∀ (τ : D.host.E →+* ℂ) x y, (l : ℂ) ^ c * τ (γ'.val x y) ∈ O ∧ (l : ℂ) ^ c * τ (γ'⁻¹.val x y) ∈ O) → ∀ Q ∈ HHa Dw.mult V.rank ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)), (∀ mo, Q.coeff mo ∈ O) → ∃ Q' ∈ HHa Dw.mult V.rank ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)), (∀ mo, Q'.coeff mo ∈ O) ∧ ∀ (M : ℕ) (e : AE D) (O₁ : Subring ℂ), M ≠ 0 → ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O₁, ((l : ℂ) ^ c') • om (a, 1) (stdF ψ θ V W sW BW f (MvPolynomial.rename lt Q)) = stdF ψ θ V W sW BW f (MvPolynomial.rename lt Q') := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP H Dw BW lt wa hrk hΨ hON hlt l c
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.RealVacPow.vacuum_det_power D ψ θ V W χV χW om ΛV ΛW sW f₀ hP Dw.p BW hON
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = ∑ ρ, ∑ j : Fin (Dw.mult ρ), wa (ρ, j) := ⟨_, rfl⟩
  refine ⟨c * d + ∑ τ, c * (V.rank * (k τ).natAbs), ?_⟩
  intro γ a γ' O hγ hrat ha hγa hden Q hQ hQO
  have hθ : IsInfFam θ := hP.1.inf
  choose σ hσ using _root_.GlobalTheory.ArchRatComp.compAt_mt_eq_map_inv D θ hθ V γ a γ' hγ hrat ha hγa
  let u : GlobalTheory.ExportSeries.GLR D V.rank := fun τ => Matrix.GeneralLinearGroup.map (σ τ) γ'⁻¹
  have hu : ∀ τ, ((u τ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) =
      Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) := fun τ => by
    rw [hσ τ]; rfl
  have hui : ∀ τ, (((u τ)⁻¹ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) =
      (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (σ τ) := fun τ => by
    simp only [u, map_inv, inv_inv]; rfl
  have hden' : ∀ τ x y, (l : ℂ) ^ c * (((u τ)⁻¹ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) x y ∈ O ∧
      (l : ℂ) ^ c * ((u τ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) x y ∈ O := fun τ x y => by
    rw [hui τ, hu τ, hσ τ]
    exact ⟨(hden (σ τ) x y).1, (hden (σ τ) x y).2⟩
  have hQ2 := GlobalTheory.T.fockSubstitution_preserves_harmonicLetterPolynomials D H Dw W.rank V.rank lt hrk hΨ hlt u wa Q hQ
  refine ⟨((l : ℂ) ^ (c * d + ∑ τ, c * (V.rank * (k τ).natAbs)) *
      ∏ τ, (Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a)).det ^ k τ) •
      MvPolynomial.rename lt.symm (GlobalTheory.ExportSeries.fockSubst (m := W.rank) (fun _ => Dw.p) u (MvPolynomial.rename lt Q)),
    GlobalTheory.smul_mem_HHa _ hQ2, ?_, ?_⟩
  · intro mo
    obtain ⟨mo', rfl⟩ := Finsupp.mapDomain_surjective lt.symm.surjective mo
    rw [MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_rename_mapDomain _ lt.symm.injective]
    have hhom : (MvPolynomial.rename lt Q).IsHomogeneous d := by
      rw [hd]
      exact (GlobalTheory.PtId.isHomogeneous_of_rowDeg Dw.mult V.rank ℂ (fun τ i => wa (τ, i)) hQ.2.2).rename_isHomogeneous
    have hcO : ∀ mo, (MvPolynomial.rename lt Q).coeff mo ∈ O := fun mo => by
      obtain ⟨mo, rfl⟩ := Finsupp.mapDomain_surjective lt.surjective mo
      rw [MvPolynomial.coeff_rename_mapDomain _ lt.injective]
      exact hQO mo
    have h1 := _root_.GlobalTheory.FockCoefInt.fockSubst_coeff_mem D W.rank V.rank (fun _ => Dw.p) u O ((l : ℂ) ^ c) hden' d _ hhom hcO mo'
    have h2 : (l : ℂ) ^ (∑ τ, c * (V.rank * (k τ).natAbs)) *
        ∏ τ, (Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a)).det ^ k τ ∈ O := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Subring.prod_mem _ fun τ _ => ?_
      rw [← hu τ, pow_mul]
      exact det_pow_mem O _ (u τ) (fun x y => (hden' τ x y).2) (fun x y => (hden' τ x y).1) (k τ)
    convert mul_mem h2 h1 using 1
    rw [pow_add, pow_mul]
    ring
  · intro M e O₁ hM f hf
    obtain ⟨hft, hff⟩ := _root_.GlobalTheory.LevelSeries.trSp_theta_fock D ψ θ V W χV χW om ΛV ΛW sW f₀ hP e M O₁ hM f hf
    rw [_root_.GlobalTheory.RealFockVac.om_stdF_subst D ψ θ V W χV χW om ΛV ΛW sW f₀ hP Dw.p BW hON a ha u hu f hft hff, hk a ha f hft hff, stdF,
      GlobalTheory.FiniteFock.pureTensorO_smul, map_smul, map_smul, MvPolynomial.rename_rename, Equiv.self_comp_symm,
      MvPolynomial.rename_id_apply, smul_smul]

end GlobalTheory.LevelSeries.ArchAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupLatticeCombOfBaseInt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.DictionaryCast
open Formalism.IndefR.FWT Formalism.L2.Pj
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw}

theorem evW_smul (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (j : Fin D.R.m) (a : D.what₂.LL) (x : S.WL ((j : ℕ) + 1)) :
    evW YS v₀ j (a • x) = sg0 D A3.A a • evW YS v₀ j x := by
  simp only [evW, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [LinearEquiv.map_smul, LinearMap.map_smulₛₗ, map_smul]
  rfl

theorem castDict_sum_smul' {V W : HSp D} (e : V = W) {m : ℕ} (a : Fin m → ℂ) (ψ : Fin m → GA D V → ℂ) (g : GA D W) :
    castDict e (∑ i, a i • ψ i) g = ∑ i, a i * castDict e (ψ i) g := by
  subst e
  simp [castDict, Finset.sum_apply]

theorem castDict_phiJ' {T : CoreJ D} {j : ℕ} {W : HSp D} {σ : T.Q.c.F →+* ℂ} (hσ : σ = T.σ₀) (h1 : T.V j σ = W)
    (h2 : T.V j T.σ₀ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D W) :
    (h1 ▸ T.phiJ j σ a f : GA D W → ℂ) g = castDict h2 (T.phiJ j T.σ₀ a f) g := by
  subst hσ
  subst h1
  rfl

end GlobalTheory.DictionaryCast

theorem GlobalTheory.XiIntCore.supLattice_comb_of_baseInt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) (b : Bool) (hV : X.core.V ((j : ℕ) + 1) X.core.σ₀ = Wc D j) (la : HeightOneSpectrum (𝓞 X.core.Q.c.F)), (∀ x : X.core.Q.c.F, FinitePlace.mk la x ≤ 1 ↔ ∃ o : D.ntw.O i, Y.Z.ρ.eO i b o = X.core.σ₀ x) → ∀ (n : ℕ) (o : Fin n → D.ntw.O i) (ψ : Fin n → (GA D (X.core.V ((j : ℕ) + 1) X.core.σ₀) → ℂ)), (∀ k, ψ k ∈ GlobalTheory.CoverRead.baseInt X.core ((j : ℕ) + 1) X.core.σ₀ (Formalism.L2.Pj.wtA (X.geo.κ j)) (X.geo.κ j).n {la}) → ∃ (n' : ℕ) (o' : Fin n' → D.ntw.O i) (m : Fin n' → NX.FmK Y.S ((j : ℕ) + 1)), (∀ k, Subtype.val (m k) ∈ (Y.S.A ((j : ℕ) + 1)).MK) ∧ FWT.castDict hV (∑ k, Y.Z.ρ.eO i b (o k) • ψ k) = ∑ k, Y.Z.ρ.eO i b (o' k) • evW Y.YS X.geo.v₀ j (Subtype.val (m k)) := by
  intro hA hR hI D X E Y hF hP i hi j b hV la hla n o ψ hψ
  have hev : X.geo.fw.Evaluates := X.geo.fw.evaluates_of_lUnif X.unif
  have hσ : FWT.res X.core (sg0 D X.A3.A) = X.core.σ₀ := by
    rw [show sg0 D X.A3.A = D.what₂.embLL from sgAt_mk _ X.R.hv0]
    exact FWT.res_embLL X.core X.geo.fw.alg_eq X.geo.fw.laws.pins.2.2.1
  have hV' : X.core.V ((j : ℕ) + 1) (FWT.res X.core (sg0 D X.A3.A)) = Wc D j := by rw [hσ]; exact hV
  have hlast : (X.geo.κ j).LastPos := fun τ k hk => by
    rw [(X.geo.fw.kap j τ).1 k]; exact GlobalTheory.LiftWeight.kapTop_lastPos D j τ k hk
  have hinR : Formalism.L2.Pj.InR D ((j : ℕ) + 1) := ⟨Nat.le_add_left _ _, j.2⟩
  have key : ∀ k, ∃ (o'' : D.ntw.O i) (m : NX.FmK Y.S ((j : ℕ) + 1)), Subtype.val m ∈ (Y.S.A ((j : ℕ) + 1)).MK ∧
      FWT.castDict hV (ψ k) = Y.Z.ρ.eO i b o'' • evW Y.YS X.geo.v₀ j (Subtype.val m) := by
    intro k
    obtain ⟨f, ⟨hsec, hhol, hint⟩, hfk⟩ := hψ k
    have hcu := GlobalTheory.CuspAllEmb.mem_cuspA_of_rdU_mem_holSub0 D X.core X.geo.fw.laws _ hinR (X.geo.κ j) hlast f hsec hhol
    let fc : FWT.Cu X.core X.geo.κ j := ⟨f, hcu⟩
    have hball : ∀ y : (X.R.FW j).Pt la, (X.R.FW j).nrm la y (X.geo.fw.e j fc) ≤ 1 := fun y => by
      rw [X.geo.fw.nrm_eq]
      exact (X.core.nrmM_le_one_iff _ la _ _).2 (hint la rfl _ (X.geo.fw.pt j la y).2)
    obtain ⟨s, hs, hsM⟩ := GlobalTheory.supLattice_localisation_of_unitBall _ _ _ _ _ (X.R.FW j) (X.integral j).2.1.2 la _ hball
    set w := X.geo.fw.e j fc with hw
    have hx₀ : evW Y.YS X.geo.v₀ j ((Y.YS.fi j).e.symm (w : Fin (X.R.nW j) → D.what₂.LL)) =
        FWT.phiC X.core hV' (Formalism.L2.Pj.wtA (X.geo.κ j)) f := by
      refine Eq.trans ?_ (hev j (sg0 D X.A3.A) (by rw [hσ]; exact X.core.toCore.good_σ₀) hV' fc)
      simp only [evW, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [LinearEquiv.apply_symm_apply]
      rfl
    have hsm : s • (w : Fin (X.R.nW j) → D.what₂.LL) =
        algebraMap X.core.Q.c.F D.what₂.LL (s : X.core.Q.c.F) • (w : Fin (X.R.nW j) → D.what₂.LL) := by
      rw [algebraMap_smul]
      exact (algebraMap_smul X.core.Q.c.F s _).symm
    let m : NX.FmK Y.S ((j : ℕ) + 1) := ⟨(Y.YS.fi j).e.symm (s • (w : Fin (X.R.nW j) → D.what₂.LL)),
      ((Y.YS.fi j).wk _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hsM.fst)⟩
    have hmK : Subtype.val m ∈ (Y.S.A ((j : ℕ) + 1)).MK :=
      ((Y.YS.fi j).mkK _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hsM)
    have hsσ : sg0 D X.A3.A (algebraMap X.core.Q.c.F D.what₂.LL (s : X.core.Q.c.F)) = X.core.σ₀ (s : X.core.Q.c.F) :=
      congrArg (fun τ : X.core.Q.c.F →+* ℂ => τ (s : X.core.Q.c.F)) hσ
    have hevm : evW Y.YS X.geo.v₀ j (Subtype.val m) =
        X.core.σ₀ (s : X.core.Q.c.F) • evW Y.YS X.geo.v₀ j ((Y.YS.fi j).e.symm (w : Fin (X.R.nW j) → D.what₂.LL)) := by
      change evW Y.YS X.geo.v₀ j ((Y.YS.fi j).e.symm (s • (w : Fin (X.R.nW j) → D.what₂.LL))) = _
      rw [hsm, LinearEquiv.map_smul, GlobalTheory.DictionaryCast.evW_smul, hsσ]
    have hs0 : (s : X.core.Q.c.F) ≠ 0 := fun h => hs (by
      rw [show s = 0 from RingOfIntegers.coe_eq_zero_iff.1 h]; exact la.asIdeal.zero_mem)
    have hinv : FinitePlace.mk la ((s : X.core.Q.c.F)⁻¹) ≤ 1 := by
      rw [map_inv₀, FinitePlace.mk_apply, (FinitePlace.norm_eq_one_iff_notMem X.core.Q.c.F la s).mpr hs, inv_one]
    obtain ⟨o'', ho''⟩ := (hla _).1 hinv
    refine ⟨o'', m, hmK, ?_⟩
    have hc : FWT.castDict hV (ψ k) = FWT.phiC X.core hV' (Formalism.L2.Pj.wtA (X.geo.κ j)) f := by
      rw [← hfk]
      funext g
      exact (GlobalTheory.DictionaryCast.castDict_phiJ' hσ hV' hV _ _ g).symm
    rw [hc, ← hx₀, hevm, ho'', smul_smul, map_inv₀, inv_mul_cancel₀ ((map_ne_zero _).2 hs0), one_smul]
  choose o'' m hm he using key
  refine ⟨n, fun k => o k * o'' k, m, hm, ?_⟩
  funext g
  rw [GlobalTheory.DictionaryCast.castDict_sum_smul', Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he k]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformisedCoverInvPhaseConstantsNormalisedDominStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedCover_invPhase_constants_normalised_dominant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ ph : ℂ, ‖ph‖ = 1 → BaseCc T R i hV ph → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → ∀ cc : C.U₂.Comp → ℂ, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) C.U₂ (castDict hV C.dict₂) (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i) cc → ∀ a, Dom a (κ i).n → ({ C with cc₂ := fun k => ph⁻¹ * cc k } : Cover T ((i : ℕ) + 1) T.σ₀).IsPinned a (κ i).n := by
  first | exact @GlobalTheory.CoverPinDom.isPinned_inv_mul | exact GlobalTheory.CoverPinDom.isPinned_inv_mul | (intros; apply GlobalTheory.CoverPinDom.isPinned_inv_mul <;> assumption)
end

