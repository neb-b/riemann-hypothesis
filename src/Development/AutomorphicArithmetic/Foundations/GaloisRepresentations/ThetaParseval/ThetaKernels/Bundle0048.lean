module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.PureProdOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0033
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0034
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DarbouxCharts.DarbouxAnti
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0035
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0016
public import Development.WeilBound.ThetaLifts.LatticeBasics.BotAsm
public import GroundTheory.AutomorphicForms.GL2.InnerProductParamHolo
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0036
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0026
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0030

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoRat
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open PositivityTheory.ThKF0.Resc in
set_option maxHeartbeats 1000000 in
theorem thetaSum_rational_invariant (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (γ : d.G) (hγ : γ ∈ rat2 σ d.Y) (Ψ : d.Fn) (hΨ : Ψ ∈ d.sch) :
    thetaSum F (d.om γ Ψ) = thetaSum F Ψ := by
  have hσ : IsCMExt F E σ := d.cm
  have hψ : IsStd d.B.ψ := d.std
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨δ, hq⟩ := exists_isQuad hσ
  have h0 : δ ≠ 0 := hq.unit.ne_zero
  obtain ⟨-, hS, hR⟩ := d.ok.dbl.weil
  have hYd : d.Y.J.det ≠ 0 := by
    obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
    intro hz
    have hee : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    have hM : (Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) *
        Matrix.fromBlocks 0 (((ε : ℤ) : E) • 1) 1 0 = 1 := by
      rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
      simp [smul_smul, hee]
    have h1 := congrArg Matrix.det hM
    rw [Matrix.det_mul, ← hε, Matrix.det_mul, Matrix.det_mul, dbl, Matrix.det_fromBlocks_zero₂₁, hz] at h1
    simp at h1
  have hκ : Fintype.card d.κ = Fintype.card (Fin d.m) * Fintype.card (Fin d.n ⊕ Fin d.n) := by
    have : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    let bE : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
    let bA := Algebra.TensorProduct.basis (AF F) bE
    haveI : Module.Free (AF F) (AE F E) := Module.Free.of_basis bA
    haveI : Module.Finite (AF F) (AE F E) := Module.Finite.of_basis bA
    have e := d.dd.e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_eq_card_basis bA, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card] at e
    simp only [Fintype.card_fin, Fintype.card_sum] at e ⊢
    omega
  obtain ⟨d₀, hd₀⟩ := exists_ratCoord h2 hκ d.dd.e d.ok.dbl.rat
  obtain ⟨a, b, hab, hA, hB⟩ : ∃ a b : E, -1 = δ * a * b ∧ IsHerm σ (a • d.A.J) ∧ IsHerm σ (b • d.Y.J) := by
    rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
    · refine ⟨1, -δ⁻¹, by field_simp, ?_, ?_⟩
      · rw [one_smul]; exact ⟨hA.herm, (herm_det hA).isUnit⟩
      · refine ⟨fun i j => by simp [hY i j, hq.anti], Ne.isUnit ?_⟩
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) hYd
    · refine ⟨-δ⁻¹, 1, by field_simp, ?_, ?_⟩
      · refine ⟨fun i j => by simp [hA.skew i j, hq.anti], Ne.isUnit ?_⟩
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) (skew_det hA)
      · rw [one_smul]; exact ⟨hY, hYd.isUnit⟩
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hab
  have hξ : (-1 : AE F E) = inclR (F := F) (AF F) δ * inclR (F := F) (AF F) a * inclR (F := F) (AF F) b := by
    rw [← map_mul, ← map_mul, ← hab, map_neg, map_one]
  have hJA : incM F (a • d.A.J) = inclR (F := F) (AF F) a • incM F d.A.J := by
    ext i j; simp [incM]
  have hJB : incM F (dbl (b • d.Y.J)) = inclR (F := F) (AF F) b • dbl (incM F d.Y.J) := by
    ext (i | i) (j | j) <;> simp [incM, dbl]
  obtain ⟨d', om', he, hS', hR', hgg⟩ := split_resc (c := cA σ) (C := adeleClass F) (ψ := d.B.ψ) (κ := d.κ) hξ
    (hb.isUnit.map (inclR (F := F) (AF F))) hJA hJB hS.toIsSplitting hR
  have hd' : ∀ x, d'.e (incM F x) = (fun i => algebraMap F (AF F) ((d₀ x).1 i), fun i => algebraMap F (AF F) ((d₀ x).2 i)) :=
    fun x => by rw [he]; exact hd₀ x
  obtain ⟨g', hg'1, hg'2⟩ := hgg γ
  have hg : ∃ γ₀ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E,
      ((g' : GL (Fin d.n ⊕ Fin d.n) (AE F E)) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) = incM F γ₀ := by
    obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.mp hγ
    refine ⟨g₀, ?_⟩
    rw [hg'1, ← hg₀]
    rfl
  rw [← hg'2]
  exact split_core hψ hq (a • d.A.J) (b • d.Y.J) hA hB d' d₀ hd' d.χ d.ok.hecke om' hS' hR' g' hg Ψ hΨ
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilThetadictPure
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.ThetaDictR.PureA PositivityTheory.SiegelWeilFormula.ThetaDictR.PureC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem pure_prod_of'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Φ : d.Fn) (P : InfinitePlace F → PX d.m d.n)
    (gf : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → v.adicCompletion F) → ℂ) (hP : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ P gf)
    (u : GL (Fin d.n) (AE F E)) (η : E)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ))
    (th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y))
    (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star)
    (g : InfinitePlace F → GL (Fin d.n) ℂ)
    (gc : ∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1)
    (l : InfinitePlace F → ℝ) (hl : ∀ w, |l w| = 1) :
    ∃ (Φf : (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ),
      HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin d.bs Φf Φv ∧
      HeckeCharacterZeroLocus.SiegelWeilU.IsProdInfFin (fun Y => d.T Φ (toMx Y * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ))
        (Gen.phiInf θ l fr g P) Φf := by
  obtain ⟨hloc, hcof, hT⟩ := hP
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ :=
    fun v Y => gf v (crdV d.bs v (toMxV v Y * Av u v))
  refine ⟨fun X => ∏ᶠ v, Φv v (HeckeCharacterZeroLocus.SiegelWeilU.projV v X), Φv,
    ⟨fun v => isSB_comp d.bs u v (gf v) (hloc v), ?_, fun X => rfl⟩, ?_⟩
  · filter_upwards [hcof, int_iff (m := d.m) d.bs u] with v hv hint
    funext Y
    show gf v _ = _
    rw [hv]
    by_cases h : Y ∈ HeckeCharacterZeroLocus.SiegelWeilU.latV d.bs v
    · rw [Set.indicator_of_mem h]
      refine (Set.indicator_of_mem ?_ _).trans rfl
      exact (hint Y).2 h
    · rw [Set.indicator_of_notMem h]
      refine Set.indicator_of_notMem ?_ _
      intro h'
      exact h ((hint Y).1 h')
  · intro X
    dsimp only
    rw [hT]
    dsimp only
    congr 1
    · unfold Gen.phiInf
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.PureB.crd_eq_k R u η θ th fr frc g gc w X, hl w, mul_one]
      rfl
    · refine finprod_congr fun v => ?_
      congr 1
      funext k
      have hZ : (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map (mapV v) =
          toMxV v (HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X)) * Av u v := by
        rw [map_mul_alg]
        congr 1
        ext a j
        simp only [Matrix.map_apply, toMx, toMxV, Matrix.of_apply, HeckeCharacterZeroLocus.SiegelWeilU.projV, HeckeCharacterZeroLocus.SiegelWeilU.projFin,
          mapV_eq]
      have h1 : HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (d.crd (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ) k).2 =
          phiV v (d.crd (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ) k) := rfl
      rw [h1, _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, ← basis_repr_map']
      simp only [crdV]
      rw [← hZ]
      rfl
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTunitHeis
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.Tunit
open PositivityTheory.SiegelWeilFormula.Tpar
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem tHeis_k : _root_.PositivityTheory.SiegelWeilFormula.THeis_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ Z X
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, -, hBx, hf, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tpar.frameData_k d
  set_option backward.isDefEq.respectTransparency false in
  constructor
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T]
    rw [Tpar.rho_rho (σ := σ) (A := d.A) (Y := d.Y) (dd := d.dd) (ψ := d.B.ψ) (X * (incM F d.b.1.toCols₂)ᵀ) (Z * (incM F d.b.1.toCols₂)ᵀ) Φ, map_smul, smul_eq_mul]
    change d.B.ψ (⅟2 * symp (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) _ _) * _ = _
    rw [symp_cols, frame_yy_A d.ok.frame, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.zero_mul, Matrix.trace_zero, neg_zero, map_zero, mul_zero, AddChar.map_zero_eq_one, one_mul, ← Matrix.add_mul]
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
    rw [hBx, Matrix.transpose_mul, ← Matrix.mul_assoc, Tpar.rho_rho (σ := σ) (A := d.A) (Y := d.Y) (dd := d.dd) (ψ := d.B.ψ) (X * (incM F d.b.1.toCols₂)ᵀ) (Z * (incM F t0.1)ᵀ * (diagCols (Fin d.n))ᵀ) Φ, map_smul, smul_eq_mul, add_comm,
      l_shift h hψ _ _ hΦ, ← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    change ⅟2 * symp (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) _ _ + -(⅟2 * symp (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) _ _) = _
    rw [darboux_anti d.dd, Matrix.mul_assoc Z, ← Matrix.transpose_mul, symp_cols, hf, Matrix.mul_one, trace_gram,
      map_neg]
    linear_combination (Algebra.trace (AF F) (AE F E) (Matrix.trace (Z * (X.map (cA σ))ᵀ * (incM F d.A.J)ᵀ))) *
      (invOf_two_add_invOf_two : (⅟(2 : AF F) + ⅟2 = 1))
end PositivityTheory.SiegelWeilFormula.Tunit
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGRallis
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
namespace UpperTheory.TP
private theorem zero_of_half_pk {U : Set ℂ} (hU : IsOpen U) (hd : ∀ z : ℂ, ∀ᶠ z' in 𝓝[≠] z, z' ∈ U) {τ : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (U ∩ {z | τ < z.re})) {t : ℝ} (ht : ∀ z : ℂ, t < z.re → z ∈ U ∧ f z = 0) {s : ℂ} (hs : s ∈ U)
    (hs' : τ < s.re) : f s = 0 := by
  have hsh : Continuous fun z : ℂ => z + (τ : ℂ) := by fun_prop
  have key := eq_zero_of_right (U := (fun z : ℂ => z + (τ : ℂ)) ⁻¹' U) (hU.preimage hsh)
    (fun z => by
      have tt : Tendsto (fun z : ℂ => z + (τ : ℂ)) (𝓝[≠] z) (𝓝[≠] (z + (τ : ℂ))) :=
        tendsto_nhdsWithin_iff.2 ⟨hsh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
          eventually_mem_nhdsWithin.mono fun w hw h => hw (add_right_cancel h)⟩
      exact tt.eventually (hd _))
    (f := fun z => f (z + (τ : ℂ)))
    (hf.comp (by fun_prop) fun z hz => ⟨hz.1, by simpa using hz.2⟩)
    (t := t - τ) (fun z hz => ⟨(ht _ (by simp; linarith [show t - τ < z.re from hz])).1,
      (ht _ (by simp; linarith [show t - τ < z.re from hz])).2⟩)
    (s := s - (τ : ℂ)) (by simpa using hs) (by simpa using hs')
  simpa using key
private theorem cpow_integral_pk {Y : Type} [MeasurableSpace Y] {μ : Measure Y} {A : Y → ℝ} {b : Y → ℂ} {t₀ q C : ℝ}
    (h0 : ∀ x, 0 < A x) (mA : Measurable A) (mb : AEStronglyMeasurable b μ) (hb : ∀ x, ‖b x‖ ≤ C * A x ^ q)
    (hi : ∀ t, t₀ ≤ t → Integrable (fun x => A x ^ t) μ) (s₀ : ℂ) :
    (∀ z : ℂ, t₀ < z.re - s₀.re + q → Integrable (fun x => (A x : ℂ) ^ (z - s₀) * b x) μ) ∧
      DifferentiableOn ℂ (fun z => ∫ x, (A x : ℂ) ^ (z - s₀) * b x ∂μ) {z : ℂ | t₀ < z.re - s₀.re + q} := by
  have mz : ∀ z : ℂ, AEStronglyMeasurable (fun x => (A x : ℂ) ^ (z - s₀) * b x) μ := fun z =>
    ((Complex.measurable_ofReal.comp mA).pow_const _).aestronglyMeasurable.mul mb
  have nz : ∀ (z : ℂ) x, ‖(A x : ℂ) ^ (z - s₀) * b x‖ ≤ |C| * A x ^ (z.re - s₀.re + q) := fun z x => by
    have p := h0 x
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos p, Complex.sub_re, Real.rpow_add p, mul_left_comm]
    exact mul_le_mul_of_nonneg_left ((hb x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg p.le _)))
      (Real.rpow_nonneg p.le _)
  refine ⟨fun z hz => ((hi _ hz.le).const_mul |C|).mono' (mz z) (.of_forall (nz z)), ?_⟩
  refine GroundTheory.Automorphic.PseudoEisenstein.differentiableOn_integral_of_bound
    (isOpen_lt continuous_const (by fun_prop)) (fun x z _ => ?_) (fun z _ => mz z) fun z hz => ?_
  · have : (A x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (h0 x).ne'
    exact (DifferentiableAt.const_cpow (by fun_prop) (Or.inl this)).mul_const _ |>.differentiableWithinAt
  · have hz' : t₀ < z.re - s₀.re + q := hz
    set u := z.re - s₀.re + q with hu
    refine ⟨(u - t₀) / 2, by linarith, fun w hw => ?_, fun x => |C| * (A x ^ (u - (u - t₀) / 2) + A x ^ (u + (u - t₀) / 2)),
      (((hi _ (by linarith)).add (hi _ (by linarith))).const_mul _), fun w hw x => ?_⟩
    · have := (Complex.abs_re_le_norm (w - z)).trans (mem_closedBall_iff_norm.1 hw)
      rw [Complex.sub_re, abs_le] at this
      show t₀ < w.re - s₀.re + q
      linarith [this.1]
    · have := (Complex.abs_re_le_norm (w - z)).trans (mem_closedBall_iff_norm.1 hw)
      rw [Complex.sub_re, abs_le] at this
      refine (nz w x).trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
      have p := h0 x
      have p1 := Real.rpow_pos_of_pos p (u - (u - t₀) / 2)
      have p2 := Real.rpow_pos_of_pos p (u + (u - t₀) / 2)
      rcases le_total 1 (A x) with h | h
      · have := Real.rpow_le_rpow_of_exponent_le h (show w.re - s₀.re + q ≤ u + (u - t₀) / 2 by linarith [this.2])
        linarith
      · have := Real.rpow_le_rpow_of_exponent_ge p h (show u - (u - t₀) / 2 ≤ w.re - s₀.re + q by linarith [this.1])
        linarith
private theorem coef_facts_pk {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G}
    (hD : IsFundamentalDomain Γ D μ) [IsFiniteMeasure (μ.restrict D)] {φ : G → ℂ} (hc : Continuous φ) {C : ℝ} (hb : ∀ g, ‖φ g‖ ≤ C)
    (hi : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) :
    Continuous (fun g => pet μ D (fun y => φ (y * g)) φ) ∧ (∃ C' : ℝ, ∀ g, ‖pet μ D (fun y => φ (y * g)) φ‖ ≤ C') ∧
      ∀ g, pet μ D (fun y => φ (y * g⁻¹)) φ = star (pet μ D (fun y => φ (y * g)) φ) := by
  have C0 : 0 ≤ C := (norm_nonneg _).trans (hb 1)
  have nb : ∀ g y, ‖φ (y * g) * star (φ y)‖ ≤ C * C := fun g y => by
    rw [norm_mul, norm_star]; exact mul_le_mul (hb _) (hb _) (norm_nonneg _) C0
  have cm : ∀ g, Continuous fun y => φ (y * g) * star (φ y) := fun g => by fun_prop
  refine ⟨continuous_of_dominated (bound := fun _ => C * C) (fun g => (cm g).aestronglyMeasurable)
    (fun g => .of_forall (nb g)) (integrable_const _) (.of_forall fun y => by fun_prop), ⟨C * C * (μ.restrict D).real Set.univ, fun g => ?_⟩, fun g => ?_⟩
  · simpa [pet] using norm_integral_le_of_norm_le_const (μ := μ.restrict D) (.of_forall (nb g))
  · let f : G → ℂ := fun y => φ y * star (φ (y * g))
    have hf : ∀ (γ : Γ) x, f (γ • x) = f x := fun γ x => by
      simp only [f, Subgroup.smul_def, smul_eq_mul, mul_assoc]
      rw [hi _ γ.2, hi _ γ.2]
    have h2 : IsFundamentalDomain Γ (MulOpposite.op g⁻¹ • D) μ := hD.smul_of_comm (MulOpposite.op g⁻¹)
    have h3 : ∫ y in MulOpposite.op g⁻¹ • D, f y ∂μ = ∫ y in D, f (y * g⁻¹) ∂μ := by
      exact (measurePreserving_mul_right μ g⁻¹).setIntegral_image_emb (measurableEmbedding_mulRight g⁻¹) f D
    have h4 := h2.setIntegral_eq hD hf
    rw [h3] at h4
    simp only [pet]
    simp only [f, inv_mul_cancel_right] at h4
    rw [h4, Complex.star_def, ← integral_conj]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp [mul_comm]
theorem _root_.UpperTheory.TP.rallis_k : _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.Rallis_k := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hP hn hd K a e hK ha he t₀ hi hlt ν hν Φ hΦ φ hφ
  have h0 : min n 0 = 0 := by simp
  have h0' : min d 0 = 0 := by simp
  have cX := T.cpt F E σ B _ X _ _ hP.base (.inl hP.herm) h0
  have cW := T.cpt F E σ B _ W _ _ hP.base (.inr hP.skew) h0'
  obtain ⟨μ, D, hμ, hD⟩ := cW.ex
  have hKc := T.stab2 F E σ B _ X _ _ hP.base (.inl hP.herm) K hK
  have hJ := _root_.GlobalTheory.ThK.Dbl.aniso_of_k hP.base (.inl hP.herm) h0
  obtain ⟨⟨K₁, a₁, hK₁, ha₁, ca, a0⟩, e₁, ce, he₁⟩ := _root_.GlobalTheory.ThK.Dbl.hgtEx_of_k T.stab2 F E σ B _ X _ _ hP.base (.inl hP.herm)
  have eK : K₁ = K := Subgroup.ext fun k => (hK₁ k).trans (hK k).symm
  subst eK
  have ea : a₁ = a := funext fun x => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa x
    rw [ha.val p t hp k hk, ha₁.val p t hp k hk]
  subst ea
  have ee : e₁ = e := MonoidHom.ext fun x => Subtype.ext (Units.ext ((he₁ x.1 x.2).trans (he x.1 x.2).symm))
  subst ee
  haveI := cX.sc; haveI := cW.sc; haveI := cX.lc; haveI := cW.lc; haveI := cX.cnt; haveI := hP.good.haar; haveI := cX.right M.μ hP.good.haar
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by rw [Measure.restrict_apply_univ]; exact cW.fin _ _ hμ hD⟩
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact cX.fin _ _ hP.good.haar hP.good.dom⟩
  obtain ⟨c, c1, hc1⟩ := inv_scale M.μ
  have s1 := T.polSch F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP Φ hΦ
  have bT := (T.basic F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP).1 Φ s1
  obtain ⟨dd, om₂, S, l, d1, d2, d3, d4⟩ := T.dbl F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP
  obtain ⟨c', c0, hc⟩ := d4 ν hν
  have c2 : (c' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 c0.ne'
  have sec := T.boxSec F E σ B _ _ _ _ M _ _ _ _ hP.base hn hd hP.herm hP.skew h0' hP.good χW hP.hW hP.resW dd om₂ S l d3 d1 K₁ a₁ hK ha Φ hΦ Φ hΦ
  obtain ⟨U, Ê, hE, u, hv⟩ := T.swFull F E σ B _ _ _ _ M _ _ _ _ hP.base hn hd hP.herm hP.skew h0' hP.good χW hP.hW hP.resW dd om₂ S l d3 d1
    K₁ a₁ hK ha μ D hμ hD Φ hΦ Φ hΦ
  set f : G2 σ X → ℂ := fun x => l (om₂ x (boxFun Φ (star Φ))) with hf
  set s₀ : ℂ := ((d : ℂ) - n) / 2 with hs₀
  have hap : ∀ g, a₁ (e₁ (1, g)) = a₁ (e₁ (g⁻¹, 1)) := fun g => by
    have := ha.mul (he g g).par (e₁ (g⁻¹, 1))
    rw [absE_det hJ, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one] at this
    simpa using this
  have hi' : ∀ t, t₀ ≤ t → Integrable (fun g => a₁ (e₁ (1, g)) ^ t) M.μ := fun t ht => by
    have h1 : Integrable (fun g => (((a₁ (e₁ (1, g)) ^ t : ℝ) : ℂ))) M.μ := (hc1 _).1 (by
      simpa [hap] using (hi t ht).ofReal (𝕜 := ℂ))
    simpa using h1.re
  have idf : ∀ g, f (e₁ (1, g)) * detInv χW g = c' * coef om ν Φ g⁻¹ := fun g => by
    have h1 := Law.diag sec.law hJ he g (e₁ (g⁻¹, 1))
    rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one] at h1
    have e2 := ((d2 Φ s1 Φ s1).2 1 g⁻¹ 1 _ (he _ _)).2
    rw [detInv_rat hP.hW (one_mem _), one_smul, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl, map_one, Module.End.one_apply] at e2
    rw [h1, hf]
    simp only [e2]
    rw [hc _ (hP.weil.isUSplitting.pres _ _ s1) _ s1, coef]
  have cF : Continuous (coef om ν Φ) := by
    have h1 : coef om ν Φ = fun g => (c' : ℂ)⁻¹ * (f (e₁ (1, g⁻¹)) * detInv χW g⁻¹) := funext fun g => by
      rw [idf, inv_inv, inv_mul_cancel_left₀ c2]
    rw [h1]
    exact continuous_const.mul ((sec.cont.comp (ce.comp (continuous_const.prodMk continuous_inv))).mul
      ((continuous_detInv hP.hW).comp continuous_inv))
  obtain ⟨Cf, hCf⟩ := Law.bound sec.law sec.cont ha hKc
  have hre : (s₀ + (n : ℂ) / 2).re = (d : ℝ) / 2 := by
    have : s₀ + (n : ℂ) / 2 = (((d : ℝ) / 2 : ℝ) : ℂ) := by rw [hs₀]; push_cast; ring
    rw [this, Complex.ofReal_re]
  have bF : ∀ g, ‖coef om ν Φ g‖ ≤ (c'⁻¹ * Cf) * a₁ (e₁ (g, 1)) ^ ((d : ℝ) / 2) := fun g => by
    have h1 := idf g⁻¹
    rw [inv_inv] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_detInv, mul_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg c0.le] at h2
    have h3 := hCf (e₁ (1, g⁻¹))
    rw [hre, hap, inv_inv, h2] at h3
    rw [mul_assoc, le_inv_mul_iff₀ c0]
    exact h3
  obtain ⟨Cφ, hCφ⟩ := cX.bdd hφ.1 hφ.2
  obtain ⟨cm, ⟨Cm, hCm⟩, im⟩ := coef_facts_pk hP.good.dom hφ.1 hCφ hφ.2
  change Continuous (mc M φ) at cm
  change ∀ g, ‖mc M φ g‖ ≤ Cm at hCm
  change ∀ g, mc M φ g⁻¹ = star (mc M φ g) at im
  have Cm0 : 0 ≤ Cm := (norm_nonneg _).trans (hCm 1)
  have a0' : ∀ g, 0 < a₁ (e₁ (g, 1)) := fun g => a0 _
  have mA : Measurable fun g => a₁ (e₁ (g, 1)) :=
    (ca.comp (ce.comp (continuous_id.prodMk continuous_const))).measurable
  have hb : ∀ g, ‖coef om ν Φ g * star (mc M φ g)‖ ≤ (c'⁻¹ * Cf * Cm) * a₁ (e₁ (g, 1)) ^ ((d : ℝ) / 2) := fun g => by
    rw [norm_mul, norm_star, mul_right_comm]
    exact mul_le_mul (bF g) (hCm g) (norm_nonneg _) ((norm_nonneg _).trans (bF g))
  obtain ⟨iZ, dZ⟩ := cpow_integral_pk a0' mA (cF.mul cm.star).aestronglyMeasurable hb hi s₀
  have hsr : s₀.re = ((d : ℝ) - n) / 2 := by
    have : s₀ = ((((d : ℝ) - n) / 2 : ℝ) : ℂ) := by rw [hs₀]; push_cast; ring
    rw [this, Complex.ofReal_re]
  have ib : Integrable (fun g => coef om ν Φ g * star (mc M φ g)) M.μ := by
    simpa using iZ s₀ (by simpa using hlt)
  refine ⟨ib, fun L0 => ?_⟩
  obtain ⟨hol, t₁, far⟩ := _root_.GlobalTheory.ThK.Dbl.kpair_cont_k hP.base (.inl hP.herm) h0 cX hP.hW he ce hKc ha ca a0 sec.cont sec.law hE hP.good.haar hP.good.dom hi'
  have rp : IsRapid φ := cX.rapid hφ.1 hφ.2
  have eqP : ∀ z : ℂ, t₁ < z.re → kpair χW e₁ M.μ M.dom (Ê z) φ =
      c * (c' * ∫ g, (a₁ (e₁ (g, 1)) : ℂ) ^ (z - s₀) * (coef om ν Φ g * star (mc M φ g)) ∂M.μ) := fun z hz => by
    have ez : ∀ g, flat a₁ f s₀ z (e₁ (1, g)) * detInv χW g * pet M.μ M.dom (fun h => φ (h * g)) φ =
        c' * ((a₁ (e₁ (g⁻¹, 1)) : ℂ) ^ (z - s₀) * (coef om ν Φ g⁻¹ * star (mc M φ g⁻¹))) := fun g => by
      have h1 : star (mc M φ g⁻¹) = pet M.μ M.dom (fun h => φ (h * g)) φ := by rw [im, star_star]; rfl
      rw [h1, flat, hap, mul_assoc (_ ^ _), idf]
      ring
    rw [(far z hz).2.2 φ rp]
    simp only [ez]
    rw [(hc1 fun g => c' * ((a₁ (e₁ (g, 1)) : ℂ) ^ (z - s₀) * (coef om ν Φ g * star (mc M φ g)))).2, integral_const_mul]
  have H0 := zero_of_half_pk (τ := t₀ + s₀.re - (d : ℝ) / 2) hE.isOpen hE.disc
    (f := fun z => kpair χW e₁ M.μ M.dom (Ê z) φ -
      c * (c' * ∫ g, (a₁ (e₁ (g, 1)) : ℂ) ^ (z - s₀) * (coef om ν Φ g * star (mc M φ g)) ∂M.μ))
    (((hol φ rp).mono Set.inter_subset_left).sub (((dZ.mono fun z hz => by
      have : t₀ + s₀.re - (d : ℝ) / 2 < z.re := hz.2
      show t₀ < z.re - s₀.re + (d : ℝ) / 2
      linarith).const_mul _).const_mul _))
    (t := t₁) (fun z hz => ⟨(far z hz).1, sub_eq_zero.2 (eqP z hz)⟩) u (by linarith)
  have cT : Continuous fun x : UA σ W.J × UA σ X.J => theta om Φ x.2 x.1 := bT.1.comp continuous_swap
  have key := An.at_value (φ := φ) (M.μ.restrict M.dom) (μ.restrict D)
    ⟨cT, cW.bdd₂ cX cT fun γ hγ δ hδ g g' => bT.2.1 δ hδ γ hγ _ _⟩ ⟨hφ.1, Cφ, hCφ⟩
  have zl : ∀ h, ∫ g in M.dom, φ g * star (theta om Φ g h) ∂M.μ = 0 := fun h => by
    have h1 : lift M om Φ φ h = 0 := congrFun L0 h
    have h2 : star (lift M om Φ φ h) = 0 := by rw [h1, star_zero]
    rw [← h2, lift, Complex.star_def, ← integral_conj]
    refine integral_congr_ae (.of_forall fun g => ?_)
    simp [mul_comm]
  simp only [zl, zero_mul, integral_zero] at key
  have hk : kpair χW e₁ M.μ M.dom (Ê s₀) φ = (if n < d then 1 else 2) * (((μ.real D)⁻¹ : ℝ) : ℂ) *
      ∫ y, (∫ h in D, theta om Φ y.1 h * star (theta om Φ y.2 h) ∂μ) * (φ y.2 * star (φ y.1)) ∂(M.μ.restrict M.dom).prod (M.μ.restrict M.dom) := by
    rw [kpair, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [hv, setAverage_eq, Complex.real_smul, ← fun g => (((d2 Φ s1 Φ s1).2 g y.1 y.2 _ (he _ _)).1), integral_const_mul]
    ring
  have H1 : c * (c' * ∫ g, coef om ν Φ g * star (mc M φ g) ∂M.μ) = 0 := by
    have h2 : kpair χW e₁ M.μ M.dom (Ê s₀) φ = 0 := by rw [hk, key, mul_zero]
    simpa [h2] using H0
  exact (mul_eq_zero.1 ((mul_eq_zero.1 H1).resolve_left c1)).resolve_left c2
end UpperTheory.TP
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaPreservingEndomorphismScalar
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_preserving_endomorphism_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ M : Module.End ℂ (WOF F E nS nT → ℂ),
      (∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (M f)) →
      (∀ w f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M (heisOF σ JS JT ξ₀ B.ψ w f) = heisOF σ JS JT ξ₀ B.ψ w (M f)) →
      (∀ (μ : MeasureTheory.Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
        MeasureTheory.IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
          ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) →
      ∃ c : ℂ, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M f = c • f := by
  first | exact @_root_.GlobalTheory.ThetaSchurF.schur_k | exact _root_.GlobalTheory.ThetaSchurF.schur_k | (intros; apply _root_.GlobalTheory.ThetaSchurF.schur_k <;> assumption)
end
end

