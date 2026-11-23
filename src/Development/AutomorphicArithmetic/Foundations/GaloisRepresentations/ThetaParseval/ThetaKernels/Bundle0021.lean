module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0008
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0016
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0015
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1508
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0019
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.SiegelGrowthForms.IsGrowFormEvAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0009
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ActsExK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKF0
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
open PositivityTheory.ThKH.Locrep
theorem actsEx_k : _root_.GlobalTheory.ThK.ActsEx_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v
  obtain ⟨ω, ρ, L⟩ := _root_.PositivityTheory.ThKH.Locrep.locRepEx_k F E σ n d B X W M om ⟨hP.base, ⟨r, s, hP.herm⟩, ⟨r', s', hP.skew⟩, hP.good, χX, χW, hP.weil⟩ v
  refine ⟨fun g hg h hh φ hφ => ⟨ω (g, h) φ, ⟨L.pres g hg h hh φ hφ, (L.acts g hg h hh φ hφ _).2 rfl⟩,
      fun φ₁ h₁ => (L.acts g hg h hh φ hφ _).1 h₁.2⟩,
    fun u hu φ hφ => ⟨ρ u φ, ⟨L.presH u hu φ hφ, (L.actsH u hu φ hφ _).2 rfl⟩,
      fun φ₁ h₁ => (L.actsH u hu φ hφ _).1 h₁.2⟩, fun φ hφ => ?_⟩
  have hs := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  let loc : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v) := fun p => res v x₀ ∘ₗ om p ∘ₗ tensL v r₀
  have hloc : ∀ p : UA σ X.J × UA σ W.J, p.1 ∈ UAt σ X (evFin F v) → p.2 ∈ UAt σ W (evFin F v) → ∀ φ ∈ SB _,
      loc p φ = ω p φ := fun p h1 h2 φ hφ =>
    (eq_of_acts v h₁ (h₀ φ hφ) ((L.acts p.1 h1 p.2 h2 φ hφ _).2 rfl)).symm
  obtain ⟨K, hK1, hK2, hK3, hK4⟩ := exists_small_subgroups σ X v
  obtain ⟨K', hK1', hK2', hK3', hK4'⟩ := exists_small_subgroups σ W v
  obtain ⟨m, hm⟩ := smooth_of_weak (SB _) (fun k => (K k).prod (K' k))
    (fun a b hab => Subgroup.prod_mono (hK1 hab) (hK1' hab))
    (fun U hU => by
      obtain ⟨U₁, h1, U₂, h2, h⟩ := mem_nhds_prod_iff.1 hU
      obtain ⟨a, ha⟩ := hK2 U₁ h1
      obtain ⟨b, hb⟩ := hK2' U₂ h2
      exact ⟨max a b, fun p hp => h ⟨ha (hK1 (le_max_left a b) hp.1), hb (hK1' (le_max_right a b) hp.2)⟩⟩)
    loc (fun p hp φ hφ => by
      rw [hloc p (hK3 0 hp.1) (hK3' 0 hp.2) φ hφ]
      exact L.pres p.1 (hK3 0 hp.1) p.2 (hK3' 0 hp.2) φ hφ)
    (fun φ hφ => by
      rw [hloc 1 (one_mem_UAt X v) (one_mem_UAt W v) φ hφ]
      exact L.one φ hφ)
    (fun p hp q hq φ hφ => by
      rw [hloc (p * q) (mul_mem_UAt (hK3 0 hp.1) (hK3 0 hq.1)) (mul_mem_UAt (hK3' 0 hp.2) (hK3' 0 hq.2)) φ hφ,
        hloc q (hK3 0 hq.1) (hK3' 0 hq.2) φ hφ,
        hloc p (hK3 0 hp.1) (hK3' 0 hp.2) _ (L.pres q.1 (hK3 0 hq.1) q.2 (hK3' 0 hq.2) φ hφ)]
      exact L.mul p.1 (hK3 0 hp.1) p.2 (hK3' 0 hp.2) q.1 (hK3 0 hq.1) q.2 (hK3' 0 hq.2) φ hφ)
    (fun l φ hφ => hs.cont _ (res_adm v x₀ l) _ (h₀ φ hφ).2) φ hφ
  obtain ⟨U, hU, hUK⟩ := hK4 m
  obtain ⟨U', hU', hUK'⟩ := hK4' m
  refine ⟨U ×ˢ U', prod_mem_nhds hU hU', fun x hx h1 h2 => ?_⟩
  refine (L.acts x.1 h1 x.2 h2 φ hφ φ).2 ?_
  rw [← hloc x h1 h2 φ hφ]
  exact (hm x ⟨hUK _ hx.1 h1, hUK' _ hx.2 h2⟩).symm
end PositivityTheory.ThKF0
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ArchimedeanChartThetaEquivariant
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_chart_theta_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ u v : IxF F nS nT → ℂ, B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v)) =
        Complex.exp (Real.pi * Complex.I * ((star v ⬝ᵥ HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *ᵥ u).im : ℂ)) := by
  first | exact @_root_.GlobalTheory.RealCharF.psi_symplOHF_iotaVF_k | exact _root_.GlobalTheory.RealCharF.psi_symplOHF_iotaVF_k | (intros; apply _root_.GlobalTheory.RealCharF.psi_symplOHF_iotaVF_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.CommFEventuallyK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.SplitLagrF
open GlobalTheory.SplitInvFormF GlobalTheory.WeilSchrodinger.DblTargetF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
variable {B : Base F E}
theorem prof_support_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {e : AEF F E} (he : IsSplitIdemF σ e)
    {f : WOF F E nS (nT + nT) → ℂ} (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) :
    ∃ K : Set (conjHalf σ e nS nT), IsCompact K ∧
      ∀ t : conjHalf σ e nS nT, t ∉ K → prof σ JS JT ξ₀ B.ψ ν 𝓕 f t = 0 := by
  obtain ⟨K, hK, hKs⟩ := _root_.GlobalTheory.SplitLagrF.exists_compact_ann_k (JS := JS) hB hS hT hξ hσξ he
    (fun g => heisOF σ JS (dblG JT) ξ₀ B.ψ (dC F E nT * ((-hlf F E) • g : WOF F E nS nT)) f = f) (fun g hg => by
      obtain ⟨k, hk, h⟩ := exists_nsmul_fix (GlobalTheory.SplitVacF.isSplitIdemF_conj he)
        (mul_mem_conjHalf (dC F E nT) (smul_mem_conjHalf (-hlf F E) hg)) hf
      refine ⟨k, hk, ?_⟩
      rwa [smul_comm, Matrix.mul_smul])
  refine ⟨K, hK, fun t ht => ?_⟩
  by_contra hne
  refine ht (hKs t fun g hg => ?_)
  have h := _root_.GlobalTheory.SplitLagrF.prof_heis_lift_k hB hS hT hξ hσξ hν h𝓕 hf g t
  rw [hg] at h
  exact (mul_eq_right₀ hne).1 h.symm
theorem prof_integrable_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {e : AEF F E} (he : IsSplitIdemF σ e)
    [MeasurableSpace (conjHalf σ e nS nT)] [BorelSpace (conjHalf σ e nS nT)]
    [IsTopologicalAddGroup (WOF F E nS nT)] (μ : Measure (conjHalf σ e nS nT)) [μ.IsAddHaarMeasure]
    {f : WOF F E nS (nT + nT) → ℂ} (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) :
    Integrable (fun t : conjHalf σ e nS nT => prof σ JS JT ξ₀ B.ψ ν 𝓕 f t) μ := by
  obtain ⟨-, i2, i3, i4, -⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  have : T2Space (conjHalf σ e nS nT) := inferInstance
  have : R1Space (conjHalf σ e nS nT) := T2Space.r1Space
  obtain ⟨U, hU, hUf⟩ := prof_level (JT := JT) ν 𝓕 he hf
  obtain ⟨K, hK, hKs⟩ := _root_.GlobalTheory.SplitLagrF.prof_support_k hB hS hT hξ hσξ hν h𝓕 he hf
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hK hKs)
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  intro t
  have hn : {s : conjHalf σ e nS nT | s - t ∈ U} ∈ nhds t := by
    refine IsOpen.mem_nhds (hU.preimage (continuous_id.sub continuous_const)) ?_
    show t - t ∈ U
    rw [sub_self]; exact U.zero_mem
  filter_upwards [hn] with s hs
  have h1 := hUf t _ hs
  rwa [add_sub_cancel] at h1
theorem commF_eventually_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) {e : AEF F E} (he : IsSplitIdemF σ e) (g : WOF F E nS nT) :
    ∀ᶠ y : conjHalf σ e nS nT in nhds 0, commF σ JS JT ξ₀ B.ψ g y = 1 := by
  have hψ : Continuous B.ψ := hB.std.1
  obtain ⟨K, hK⟩ := GlobalTheory.HeisThetaF.exists_openAddSubgroup_psi_fin B.ψ hψ
  let φ : WOF F E nS nT → AF F := fun u => symplOHF σ JS JT ξ₀ g u - symplOHF σ JS JT ξ₀ u g
  have hφ : Continuous φ :=
    (GlobalTheory.HeisThetaF.continuous_symplOHF_right g).sub (GlobalTheory.HeisThetaF.continuous_symplOHF_left g)
  let ρ : conjHalf σ e nS nT → Af F := fun u => (φ u.1).2
  have hρ : Continuous ρ := continuous_snd.comp (hφ.comp continuous_subtype_val)
  have h0 : ρ 0 = 0 := by
    show (symplOHF σ JS JT ξ₀ g 0 - symplOHF σ JS JT ξ₀ 0 g).2 = 0
    rw [GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero]
    rfl
  have hn : ρ ⁻¹' (K : Set (Af F)) ∈ nhds (0 : conjHalf σ e nS nT) :=
    (K.isOpen.preimage hρ).mem_nhds (by rw [Set.mem_preimage, h0]; exact K.zero_mem)
  filter_upwards [hn] with u hu
  have h1 : pairA F 1 0 • u.1 = 0 :=
    GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF (GlobalTheory.SplitVacF.fin_of_mem he u.2)
  have hfst : fstA F (φ u.1) = 0 := by
    rw [← GlobalTheory.HeisThetaF.fstA_mul_idem]
    show fstA F (pairA F 1 0 * (symplOHF σ JS JT ξ₀ g u.1 - symplOHF σ JS JT ξ₀ u.1 g)) = 0
    rw [mul_sub, ← GlobalTheory.HeisThetaF.symplOHF_smul_left (pairA F 1 0) u.1 g,
      ← GlobalTheory.HeisThetaF.symplOHF_smul_right (pairA F 1 0) g u.1, h1, GlobalTheory.HeisThetaF.symplOHF_zero_left,
      GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero, map_zero]
  have hφu : φ u.1 = pairA F 0 (ρ u) := Prod.ext hfst rfl
  show B.ψ (φ u.1) = 1
  rw [hφu]
  exact hK _ hu
theorem lagrInt_eq_zero_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {e : AEF F E} (he : IsSplitIdemF σ e)
    [MeasurableSpace (conjHalf σ e nS nT)] [BorelSpace (conjHalf σ e nS nT)]
    [IsTopologicalAddGroup (WOF F E nS nT)] (μ : Measure (conjHalf σ e nS nT)) [μ.IsAddHaarMeasure]
    {f : WOF F E nS (nT + nT) → ℂ} (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f)
    (hall : ∀ u, ∫ t : conjHalf σ e nS nT, prof σ JS JT ξ₀ B.ψ ν 𝓕 (heisOF σ JS (dblG JT) ξ₀ B.ψ u f) t ∂μ = 0) :
    GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT) f = 0 := by
  obtain ⟨U, hU, hUf⟩ := prof_level (JT := JT) ν 𝓕 he hf
  obtain ⟨K, hK, hKs⟩ := _root_.GlobalTheory.SplitLagrF.prof_support_k hB hS hT hξ hσξ hν h𝓕 he hf
  obtain ⟨G, -, hG⟩ := _root_.GlobalTheory.SplitLagrF.exists_open_sep_k (JS := JS) hB hS hT hξ hσξ he U hU
  let L : AddSubgroup (conjHalf σ e nS nT) :=
    { carrier := {y | ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) = 1}
      add_mem' := fun {a b} ha hb g hg => by
        rw [AddSubgroup.coe_add, GlobalTheory.SplitVacF.commF_add_right, ha g hg, hb g hg, one_mul]
      zero_mem' := fun g _ => GlobalTheory.SplitVacF.commF_zero_right g
      neg_mem' := fun {a} ha g hg => by
        have := GlobalTheory.SplitVacF.commF_neg_right (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) g
          (a : WOF F E nS nT)
        rwa [ha g hg, mul_one] at this }
  have hL : IsOpen (L : Set (conjHalf σ e nS nT)) := by
    refine AddSubgroup.isOpen_of_mem_nhds L (g := 0) ?_
    exact (Filter.eventually_all_finset G).2 fun g _ => _root_.GlobalTheory.SplitLagrF.commF_eventually_k hB he g
  have hφ := GlobalTheory.fourier_uniqueness_of_openSubgroup μ
    (fun (a : WOF F E nS nT) (t : conjHalf σ e nS nT) => commF σ JS JT ξ₀ B.ψ a t)
    (fun a s t => GlobalTheory.SplitVacF.commF_add_right a s.1 t.1)
    (fun a => GlobalTheory.SplitVacF.commF_zero_right a) (fun t => GlobalTheory.SplitVacF.commF_zero_left t.1)
    (fun a b t => GlobalTheory.SplitVacF.commF_add_left a b t.1) L hL
    (fun x hx => by
      have hx' : ¬ ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (x : WOF F E nS nT) = 1 := hx
      push_neg at hx'
      obtain ⟨g, hg, hne⟩ := hx'
      exact ⟨g, fun l hl => hl g hg, hne⟩)
    (fun t => prof σ JS JT ξ₀ B.ψ ν 𝓕 f t) K hK hKs (fun t l hl => hUf t l (hG l hl))
    (fun a _ => by
      rw [← hall (dC F E nT * ((-hlf F E) • a : WOF F E nS nT))]
      simp only [_root_.GlobalTheory.SplitLagrF.prof_heis_lift_k hB hS hT hξ hσξ hν h𝓕 hf])
  rw [← prof_zero (σ := σ) (JS := JS) (JT := JT) (ξ₀ := ξ₀) (ψ := B.ψ)]
  exact congrFun hφ 0
end GlobalTheory.SplitLagrF
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContDiffThetaTrRealCMK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
namespace GlobalTheory.ThetaSmoothCM
theorem contDiff_thetaTr_real_CM_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L →
            (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
            ∀ w, ContDiff ℝ ∞ fun t => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (w + L t) := by
  intro F E _ _ _ _ _ σ B hgood nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ hψ JA JB ξ hJA hJB κ _ co hrat φ hφ k L hLc hLf w
  exact _root_.GlobalTheory.T.doubled_lagrangian_invariant_functional F E σ B hgood hψ nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ JA JB ξ hJA hJB κ co hrat φ hφ k L hLc hLf w
end GlobalTheory.ThetaSmoothCM
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledThetaLiftAutomorphy
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_theta_lift_automorphy : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          Continuous (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) := by
  first | exact @_root_.GlobalTheory.ThetaTrContCM.continuous_thetaTr_cm_k | exact _root_.GlobalTheory.ThetaTrContCM.continuous_thetaTr_cm_k | (intros; apply _root_.GlobalTheory.ThetaTrContCM.continuous_thetaTr_cm_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledThetaLiftConvergence
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_theta_lift_convergence : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∃ U : AddSubgroup (Formalism.IndefR.DatumF.WOF F E nS nT), IsOpen (U : Set (Formalism.IndefR.DatumF.WOF F E nS nT)) ∧
            ∀ u ∈ U, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 →
              Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ u (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) =
                GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ := by
  first | exact @_root_.GlobalTheory.ThetaLevelCM.thetaTr_level_k | exact _root_.GlobalTheory.ThetaLevelCM.thetaTr_level_k | (intros; apply _root_.GlobalTheory.ThetaLevelCM.thetaTr_level_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledThetaLiftIdentity
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_theta_lift_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : Formalism.IndefR.DatumF.WOF F E nS nT),
            GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (Formalism.IndefR.DatumF.ratWF γ + w) =
              B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) *
                GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ w := by
  first | exact @_root_.GlobalTheory.ThetaQuasiRatCM.thetaTr_ratWF_add_quasi_k | exact _root_.GlobalTheory.ThetaQuasiRatCM.thetaTr_ratWF_add_quasi_k | (intros; apply _root_.GlobalTheory.ThetaQuasiRatCM.thetaTr_ratWF_add_quasi_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisBLOfK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace SiegelEisensteinSeries.BRoad
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
theorem eisBL_of_k (hH : _root_.SiegelEisensteinSeries.EisHalf_k) (hM : _root_.SiegelEisensteinSeries.BRoad.SiegelMult_k) (hF : OneVarFactor) : _root_.GlobalTheory.ThK.Dbl.EisBL_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY χ hχ c hc b K a hb hK ha s₁ f hf
  obtain ⟨t₀, v, hv, hvh⟩ := hH F E σ B n Y r s hB hn hY χ hχ c hc b K a hb hK ha s₁ f hf
  obtain ⟨A, H, t₁, hA, hAne, hHh, hHs⟩ := hM F E σ B n Y r s hB hn hY χ hχ c hc b K a hb hK ha s₁ f hf
  have hHv : ∀ s' : ℂ, max t₀ t₁ < s'.re → ∀ x, (H s').1 x = A s' * (v s').1 x := by
    intro s' hs' x
    have h1 := hHs s' (lt_of_le_of_lt (le_max_right _ _) hs') x
    have h2 := (hv s' (lt_of_le_of_lt (le_max_left _ _) hs') x).mul_left (A s')
    exact h1.unique h2
  let Ehat : ℂ → G2 σ Y → ℂ := fun s' x => if max t₀ t₁ < s'.re then (v s').1 x else (H s').1 x / A s'
  refine ⟨Ehat, ⟨max t₀ t₁, ?_, ?_⟩, ?_⟩
  · intro s' hs' x
    simp only [Ehat, if_pos hs']
    exact hv s' (lt_of_le_of_lt (le_max_left _ _) hs') x
  · intro x
    have hd : DifferentiableOn ℂ (fun s' => evAt x (v s')) {s' : ℂ | t₀ < s'.re} :=
      hvh (evAt x) (isGrowForm_evAt x)
    have hd' : DifferentiableOn ℂ (fun s' => (v s').1 x) {s' : ℂ | max t₀ t₁ < s'.re} :=
      (hd.mono fun s' (hs' : max t₀ t₁ < s'.re) => (show t₀ < s'.re from lt_of_le_of_lt (le_max_left _ _) hs'))
    refine hd'.congr fun s' hs' => ?_
    simp only [Ehat, if_pos (show max t₀ t₁ < s'.re from hs')]
  · intro s₀
    obtain ⟨k, U, u, hUo, hs₀U, hud, hUA⟩ := hF A hA hAne s₀
    refine ⟨k, U, fun s' => (u s')⁻¹ • H s', hUo.mem_nhds hs₀U, ?_, ?_⟩
    · intro s' hs' hne x
      obtain ⟨hu, hAs⟩ := hUA s' hs'
      have hpow : (s' - s₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hne)
      show (u s')⁻¹ * (H s').1 x = (s' - s₀) ^ k * Ehat s' x
      by_cases hre : max t₀ t₁ < s'.re
      · simp only [Ehat, if_pos hre]
        rw [hHv s' hre x, hAs]
        field_simp
      · simp only [Ehat, if_neg hre]
        rw [hAs]
        field_simp
    · intro μ hμ
      have h1 : DifferentiableOn ℂ (fun s' => (u s')⁻¹) U := hud.inv fun s' hs' => (hUA s' hs').1
      have h2 : DifferentiableOn ℂ (fun s' => μ (H s')) U := (hHh μ hμ).differentiableOn
      refine (h1.mul h2).congr fun s' _ => ?_
      simp [map_smul, smul_eq_mul]
end SiegelEisensteinSeries.BRoad
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EndEgrpMatch
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
set_option linter.unusedSectionVars false
namespace PositivityTheory.ThKEnd.Grp
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
theorem level_sch_k (hL : _root_.PositivityTheory.ThKEst.Level_k) {n : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW om r s r' s'}
    (hp : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) :
    ∀ᶠ u in 𝓝 (1 : UA σ W.J), (∀ w, (mat u).map (piInf (B.emb w)) = 1) → om (1, u) Φ = Φ := by
  induction hΦ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨U, hU, h⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp g hg
    exact mem_of_superset hU fun u hu k => h u hu k f
  | zero => exact Eventually.of_forall fun _ _ => map_zero _
  | add x y _ _ hx hy => filter_upwards [hx, hy] with u h1 h2 k using by rw [map_add (f := _), h1 k, h2 k]
  | smul a x _ hx => filter_upwards [hx] with u h1 k using by rw [map_smul, h1 k]
variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'}
  {Rf : FinMaps F a a'}
end PositivityTheory.ThKEnd.Grp
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HeightContinuousPosK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
noncomputable section
namespace GlobalTheory.CompanionTheory.Iwasawa
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem height_continuous_pos_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → Continuous a ∧ ∀ x, 0 < a x :=
  fun F E _ _ _ _ _ σ B n Y r s hB hn hY b K a hb hK ha =>
    continuous_pos (_root_.GlobalTheory.T.isCompact_standard_maximal_compact F E σ B n Y r s hB hn hY b K a hb hK ha) ha
end GlobalTheory.CompanionTheory.Iwasawa
end
end
end

