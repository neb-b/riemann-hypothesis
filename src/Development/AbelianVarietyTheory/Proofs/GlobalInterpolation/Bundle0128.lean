module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodular
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdChar
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0034
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0009
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemen
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabTransitiveOfLemmas
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0039
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupHaarPropertiesProof
section
namespace GlobalTheory

theorem adelicUnitaryHaar_holds : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  exact ⟨_root_.GlobalTheory.AdelicStabUnimod.unimodularOver_adele F E σ hσ M J hJ, _root_.GlobalTheory.ArchUnitaryUnimod.unimodularOver_infinite F E σ hσ M J hJ,
    _root_.GlobalTheory.FiniteAdelicUnimod.unimodularOver_finiteAdele F E σ hσ M J hJ, _root_.GlobalTheory.LocalUnitaryUnimod.unimodularOver_adicCompletion F E σ hσ M J hJ,
    GlobalTheory.T.unitaryRationalPoints_countable_discrete_fundDomains_cm F E σ hσ M J hJ, _root_.GlobalTheory.RationalStabiliserDomains.isDiscreteWithDomains_HstabFin F E σ hσ M J hJ⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EvenThetaFunctionCmLatticeIntegralSplitPrime
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

noncomputable section

namespace GlobalTheory.MomN

open GlobalTheory.MomOne
open scoped ComplexConjugate

theorem latInt_th0_of_split_prime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → LatInt ι (Ω / ι δ₀) (lamOf D cc δ) B.th0 := by
  intro D cc δ B hcc _ q _ hq2 hjac hcop ι δ₀ θ Ω hPer
  obtain ⟨hdp, hd16, hOK, -, hlat⟩ := _root_.GlobalTheory.MomDict.main D
  obtain ⟨hTh, -, -, -, -, -, M, hMι, hMOK, hMch⟩ := hPer
  have hcc0 : cc ≠ ⊥ := hcc.1
  obtain ⟨hA, hmem⟩ := hlat cc δ hcc0
  have hmem1 := (hlat ⊤ 1 top_ne_bot).2
  have hqp : q.Prime := Fact.out
  have hN0 : Ideal.absNorm cc ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hcc0
  have hNc : ((Ideal.absNorm cc : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hsd : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast hdp.pos)
  have hAF : Formalism.L2.Th1.F.area B.L = Complex.normSq δ * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 := by
    rw [← hA]; exact B.areaOK.symm
  have hApos : 0 < Formalism.L2.Th1.F.area B.L := Formalism.L2.Th1.F.PeriodAreaSignLemmas.area_pos B.L
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    rw [hAF] at hApos
    simp at hApos
  have hmemL : ∀ x, x ∈ B.L.lattice ↔ x ∈ lamOf D cc δ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B
  obtain ⟨hGd0, hG00, -, hzero, hlaw⟩ :=
    Formalism.L2.Th1.F.th0Basic B.L B.ω₀ B.omega_mem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.half B)
  set N : ℕ := Ideal.absNorm cc with hN
  set G : ℂ → ℂ := fun z => B.th0 (δ * N * z) with hG
  have hGd : Differentiable ℂ G := by
    have : Differentiable ℂ fun z : ℂ => δ * N * z := by fun_prop
    exact hGd0.comp this
  have hG0 : G 0 = 1 := by simp only [hG, mul_zero]; exact hG00
  have hsplit : Split D.host.d q := Or.inr ⟨hq2, hjac⟩

  have hzer : ∀ z, G z = 0 → PrimeTo D.host.d q z := by
    intro z hz
    have h1 : δ * N * z + B.ω₀ / 2 ∈ B.L.lattice := (hzero _).1 hz
    have h2 : δ * ((2 * N : ℕ) * z) ∈ B.L.lattice := by
      have e : δ * ((2 * N : ℕ) * z) = (δ * N * z + B.ω₀ / 2) + (δ * N * z + B.ω₀ / 2) - B.ω₀ := by
        push_cast; ring
      rw [e]
      exact B.L.lattice.sub_mem (B.L.lattice.add_mem h1 h1) B.omega_mem
    obtain ⟨y, -, hy⟩ := (hmem _).1 ((hmemL _).1 h2)
    refine ⟨2 * N, Nat.mul_pos two_pos (Nat.pos_of_ne_zero hN0), Nat.Coprime.mul_left ?_ hcop, ?_⟩
    · exact (Nat.coprime_primes Nat.prime_two hqp).2 (Ne.symm hq2)
    · exact (hOK _).2 ⟨y, mul_left_cancel₀ hδ0 hy⟩

  have hkey : ∀ z w : ℂ, Formalism.L2.Th1.F.herm B.L (δ * N * z) (δ * N * w) = N * h1 D.host.d z w := by
    intro z w
    have hc : δ * conj δ = (Complex.normSq δ : ℂ) := Complex.mul_conj δ
    have hδn : (Complex.normSq δ : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.2 hδ0).ne'
    have hsc : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsd.ne'
    have hA0 : ((Complex.normSq δ * (N : ℝ) * Real.sqrt D.host.d / 2 : ℝ) : ℂ) ≠ 0 := by
      have : 0 < Complex.normSq δ * (N : ℝ) * Real.sqrt D.host.d / 2 := by
        have := Complex.normSq_pos.2 hδ0
        have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
        positivity
      exact_mod_cast this.ne'
    have hs2 : (2 / ((Real.sqrt D.host.d : ℝ) : ℂ)) * ((Real.sqrt D.host.d : ℝ) : ℂ) = 2 := by
      field_simp
    rw [Formalism.L2.Th1.F.herm, hAF, h1, div_eq_iff hA0]
    simp only [map_mul, Complex.conj_natCast]
    push_cast
    linear_combination ((N : ℂ) ^ 2 * z * conj w) * hc - ((N : ℂ) ^ 2 * z * conj w * (Complex.normSq δ : ℂ) / 2) * hs2
  have hlaw' : ∀ x, InOK D.host.d x → ∀ z, G (z + x) * (Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) * Complex.exp (-(Real.pi : ℂ) * h1 D.host.d z x - (Real.pi : ℂ) / 2 * h1 D.host.d x x)) ^ N = G z := by
    intro x hx z
    obtain ⟨o, ho⟩ := (hOK x).1 hx
    have hω : δ * N * x ∈ B.L.lattice := by
      refine (hmemL _).2 ((hmem _).2 ⟨(N : 𝓞 D.host.K) * o, cc.mul_mem_right _ (Ideal.absNorm_mem cc), ?_⟩)
      rw [ho]; push_cast; rw [map_mul, map_natCast]; ring
    have hl := hlaw _ hω (δ * N * z)
    rw [← Formalism.L2.Th1.F.thetaZeroCharacter] at hl
    rw [← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.char_eq (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B) B.omega_mem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hθ B)
      (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hθ' B) (by omega) _ hω, hkey, hkey] at hl
    have ha : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa B.L D.host.d (δ * N * x) = 1 ∨
        Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa B.L D.host.d (δ * N * x) = -1 := by
      rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.char_eq
        (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B) B.omega_mem
        (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hθ B)
        (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hθ' B) (by omega) _ hω]
      exact Formalism.L2.Th1.H.th0Char_pm B.L B.ω₀ _ B.omega_mem hω
    have hq1 : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.q1 B.L D.host.d (δ * N * x) = N * Complex.normSq x := by
      rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.q1, hkey, h1, Complex.mul_conj]
      have : ((N : ℂ) * (((2 / Real.sqrt D.host.d : ℝ) : ℂ) * ((Complex.normSq x : ℝ) : ℂ))).re
          = N * (2 / Real.sqrt D.host.d) * Complex.normSq x := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
      rw [this]; field_simp
    have hapow : Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) ^ N
        = Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa B.L D.host.d (δ * N * x) := by
      rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa, hq1, ← Complex.exp_nat_mul]
      congr 1; push_cast; ring
    have e1 : G (z + x) = B.th0 (δ * N * z + δ * N * x) := by
      simp only [hG]; congr 1; ring
    have e2 : G z = B.th0 (δ * N * z) := rfl
    rw [e1, e2, Base.th0, hl, mul_pow, hapow, ← Complex.exp_nat_mul]
    set a := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa B.L D.host.d (δ * N * x)
    have haa : a * a = 1 := by rcases ha with h | h <;> rw [h] <;> norm_num
    have hE : Complex.exp ((Real.pi : ℂ) * (N * h1 D.host.d z x) + (Real.pi : ℂ) * (N * h1 D.host.d x x) / 2)
        * Complex.exp (N * (-(Real.pi : ℂ) * h1 D.host.d z x - (Real.pi : ℂ) / 2 * h1 D.host.d x x)) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; ring
    linear_combination (Complex.exp ((Real.pi : ℂ) * (N * h1 D.host.d z x) + (Real.pi : ℂ) * (N * h1 D.host.d x x) / 2)
        * Complex.exp (N * (-(Real.pi : ℂ) * h1 D.host.d z x - (Real.pi : ℂ) / 2 * h1 D.host.d x x))
        * Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2) (δ * N * z)) * haa
      + (Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2) (δ * N * z)) * hE

  have hbd : Bd 1 (hat ι (PowerSeries.C (Ω / ι δ₀) * logS) G) := by
    have := _root_.GlobalTheory.MomN.ThetaQuot.bd_one_hat_of_theta_level D.host.d q M (Ω / ι δ₀) θ G N hdp hd16 hsplit hq2 hMOK hMch hTh hGd hG0 hlaw' hzer
    rwa [hMι] at this
  have hmom := GlobalTheory.T.jetsAreBoundedMeasureMoments_of_chart_coeff_bound q ι (Ω / ι δ₀) G hGd hbd
  have hspan : LatInt ι (Ω / ι δ₀) (lamOf D ⊤ 1) G := by
    refine _root_.GlobalTheory.MomN.latInt_of_span q ι ℂ D.host.d (Ω / ι δ₀) (lamOf D ⊤ 1) Unit (fun _ => (1 : ℂ)) G hdp hd16 hsplit ?_ ?_
    · intro x hx
      obtain ⟨y, -, hy⟩ := (hmem1 x).1 hx
      refine ⟨1, Nat.coprime_one_left _, fun _ => x, fun _ => (hOK x).2 ⟨y, by rw [hy, one_mul]⟩, ?_⟩
      simp
    · convert hmom using 2
      simp
  have hδN : δ * (N : ℂ) ≠ 0 := mul_ne_zero hδ0 hNc
  have hpull := _root_.GlobalTheory.MomN.latInt_pull q ι ℂ ℂ (Ω / ι δ₀) (lamOf D ⊤ 1) (lamOf D cc δ)
    ((δ * N)⁻¹ • ContinuousLinearMap.id ℂ ℂ) G hGd.contDiff ?_ hspan
  · convert hpull using 1
    funext z
    simp only [hG, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    congr 1
    field_simp
  · intro x hx
    obtain ⟨y, -, hy⟩ := (hmem x).1 hx
    refine ⟨N, hcop, (hmem1 _).2 ⟨y, trivial, ?_⟩⟩
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, nsmul_eq_mul, hy]
    field_simp

end GlobalTheory.MomN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelicUnitaryComplementRangeStabiliser
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.StabiliserOfVector

open Formalism.UG (cT UJ)
open GlobalTheory.FrameStep

theorem exists_of_conj_fixed {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {y : E} (hy : σ y = y) :
    ∃ a : F, algebraMap F E a = y := by
  obtain ⟨-, hE, h2, hτ⟩ := hCM
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let K : Submodule F E := LinearMap.ker (σ.toLinearMap - LinearMap.id)
  have hK : ∀ z, z ∈ K ↔ σ z = z := fun z => by simp [K, sub_eq_zero]
  have hne : K ≠ ⊤ := by
    intro h
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext z
    have hz : σ z = z := (hK z).1 (h ▸ Submodule.mem_top)
    have := hτ τ z
    rw [hz] at this
    exact this.symm
  have hlt := Submodule.finrank_lt hne
  have hle : Submodule.span F {(1 : E)} ≤ K := by
    rw [Submodule.span_singleton_le_iff_mem, hK, map_one]
  have heq : Submodule.span F {(1 : E)} = K := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [finrank_span_singleton one_ne_zero]
    omega
  have hmem : y ∈ Submodule.span F {(1 : E)} := heq ▸ (hK y).2 hy
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨a, by rw [← ha, Algebra.algebraMap_eq_smul_one]⟩

theorem mem_ratPts_iff {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] [Nontrivial R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (g : HA R σ J) :
    g ∈ ratPts R σ J ↔ ∃ k : Matrix (Fin M) (Fin M) E, k.map (inclR (F := F) R) =
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, congrArg (fun u : GL (Fin M) (R ⊗[F] E) => (u : Matrix (Fin M) (Fin M) (R ⊗[F] E))) hk⟩
  · rintro ⟨k, hk⟩
    have hinj : Function.Injective (inclR (F := F) (E := E) R) := (inclR (F := F) (E := E) R).injective
    have hdet : k.det ≠ 0 := by
      intro h0
      have hu : IsUnit (k.map (inclR (F := F) R)).det := by
        rw [hk]; exact (Matrix.isUnits_det_units _)
      have h1 := (inclR (F := F) (E := E) R).map_det k
      rw [h0, map_zero] at h1
      rw [RingHom.mapMatrix_apply] at h1
      rw [← h1] at hu
      exact not_isUnit_zero hu
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero k hdet, ?_, Units.ext hk⟩
    show cT (σ : E →+* E) k * J * k = J
    apply Matrix.map_injective hinj
    have hg : cT (sigR R σ) (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := g.2
    rw [← hk, cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul] at hg
    exact hg

theorem exists_hom_range_stabiliser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M M' : ℕ) (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E) (B : Matrix (Fin M) (Fin M') E) (x : Fin 1 → Fin M → E), M' + 1 = M → IsHermND σ J → IsHermND σ J' → Formalism.UG.cT (σ : E →+* E) B * J * B = J' → (∀ j, hE σ J (x 0) (fun i => B i j) = 0) → hE σ J (x 0) (x 0) ≠ 0 → ∃ φ : HA (AF F) σ J' →* HA (AF F) σ J, Continuous φ ∧ Function.Injective φ ∧ φ.range = Hstab (AF F) σ J x ∧ (∀ g, FrameRel J J' B (φ g) g) ∧ ∀ g, φ g ∈ ratPts (AF F) σ J ↔ g ∈ ratPts (AF F) σ J' := by
  intro F E _ _ _ _ _ σ hCM M M' J J' B x hM hJ hJ' hBB hxB hxx
  subst hM
  have hσ : ∀ y, σ (σ y) = y := by
    intro y
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  have hfix : σ (hE σ J (x 0) (x 0)) = hE σ J (x 0) (x 0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hE, Formalism.UG.hform, map_sum, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hJ.1 i j]
    show σ (σ (x 0 j)) * J i j * σ (x 0 i) = σ (x 0 i) * J i j * x 0 j
    rw [hσ]; ring
  obtain ⟨a, ha⟩ := exists_of_conj_fixed σ hCM hfix
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hxx (by rw [← ha, map_zero])
  have h : GlobalTheory.GaugeEx.StepData σ J x a B J' := ⟨hJ, ha0, ha.symm, hxB, hBB.symm, hJ'⟩
  obtain ⟨-, L₁, L, c, hL, h11, h21, h22, hsum, hXB, hBX⟩ := exists_dual σ hσ h
  have : Nontrivial (AF F) := inferInstanceAs (Nontrivial (InfiniteAdeleRing F × _))
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  set X : Matrix (Fin (M' + 1)) (Fin 1) E := (Matrix.of x).transpose with hXdef
  set ι : E →+* AF F ⊗[F] E := inclR (AF F) with hι
  have hone : ∀ k : ℕ, (1 : Matrix (Fin k) (Fin k) E).map ι = 1 := fun k =>
    Matrix.map_one _ (map_zero ι) (map_one ι)
  have hzero : ∀ k l : ℕ, (0 : Matrix (Fin k) (Fin l) E).map ι = 0 := fun k l =>
    Matrix.map_zero _ (map_zero ι)
  have h22' : L.map ι * B.map ι = 1 := by rw [← Matrix.map_mul, h22, hone]
  have hsum' : X.map ι * L₁.map ι + B.map ι * L.map ι = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add ι), hsum, hone]
  have hS : ∀ g : HA (AF F) σ J, g ∈ Hstab (AF F) σ J x ↔
      ((HA.mat (AF F) σ J g : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
        Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) * X.map ι = X.map ι := by
    intro g
    refine MulAction.mem_stabilizer_iff.trans ⟨fun hg => ?_, fun hg => ?_⟩
    · ext i j
      exact congrFun (congrFun hg j) i
    · funext j i
      exact congrFun (congrFun hg i) j
  obtain ⟨e, he⟩ : ∃ e : Hstab (AF F) σ J x ≃* HA (AF F) σ J',
      ∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g) :=
    exists_equiv (sigR (AF F) σ) (JR (AF F) J) (JR (AF F) J') (X.map ι) (B.map ι) (L₁.map ι)
      (L.map ι) (c.map ι)
      (by rw [hL, Matrix.map_mul, Matrix.map_mul, cT_map]; rfl)
      (by rw [← Matrix.map_mul, h11, hone]) (by rw [← Matrix.map_mul, h21, hzero]) h22' hsum'
      (by rw [cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul, hXB, hzero])
      (by rw [cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul, hBX, hzero])
      (by rw [cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul, hBB]; rfl)
      (Hstab (AF F) σ J x) hS
  let φ : HA (AF F) σ J' →* HA (AF F) σ J :=
    (Hstab (AF F) σ J x).subtype.comp e.symm.toMonoidHom
  have hφ : ∀ g, φ g = (e.symm g : HA (AF F) σ J) := fun g => rfl
  have hrel : ∀ g, FrameRel J J' B (φ g) g := by
    intro g
    have := he (e.symm g)
    rwa [MulEquiv.apply_symm_apply] at this
  have hfor : ∀ g, ((HA.mat (AF F) σ J' g : GL (Fin M') (AF F ⊗[F] E)) :
      Matrix (Fin M') (Fin M') (AF F ⊗[F] E)) =
        L.map ι * ((HA.mat (AF F) σ J (φ g) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
        Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) * B.map ι := by
    intro g
    have hr := hrel g
    rw [FrameRel, ← hι] at hr
    rw [Matrix.mul_assoc]
    erw [hr, ← Matrix.mul_assoc, h22', Matrix.one_mul]
  have hback : ∀ g, ((HA.mat (AF F) σ J (φ g) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
        Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) =
        X.map ι * L₁.map ι +
          B.map ι * ((HA.mat (AF F) σ J' g : GL (Fin M') (AF F ⊗[F] E)) :
            Matrix (Fin M') (Fin M') (AF F ⊗[F] E)) * L.map ι := by
    intro g
    have hr := hrel g
    rw [FrameRel, ← hι] at hr
    have h3 := congrArg (((HA.mat (AF F) σ J (φ g) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
      Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) * ·) hsum'
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_one] at h3
    rw [(hS (φ g)).1 (e.symm g).2] at h3
    erw [hr] at h3
    exact h3.symm
  have cm : Continuous fun g : HA (AF F) σ J' => HA.mat (AF F) σ J' g := continuous_subtype_val
  have cφ : ∀ f : HA (AF F) σ J' → HA (AF F) σ J',
      (Continuous fun g => ((HA.mat (AF F) σ J' (f g) : GL (Fin M') (AF F ⊗[F] E)) :
            Matrix (Fin M') (Fin M') (AF F ⊗[F] E))) →
      Continuous fun g => ((HA.mat (AF F) σ J (φ (f g)) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
        Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) := by
    intro f hf
    simp only [hback]
    exact continuous_const.add ((continuous_const.matrix_mul hf).matrix_mul continuous_const)
  refine ⟨φ, ?_, Subtype.val_injective.comp e.symm.injective, ?_, hrel, fun g => ?_⟩
  · refine continuous_into (AF F) σ J _ (cφ id (Units.continuous_val.comp cm)) ?_
    simp only [← map_inv]
    exact cφ (fun g => g⁻¹) (Units.continuous_coe_inv.comp cm)
  · ext h
    constructor
    · rintro ⟨g, rfl⟩
      exact (e.symm g).2
    · intro hh
      exact ⟨e ⟨h, hh⟩, by rw [hφ, MulEquiv.symm_apply_apply]⟩
  · rw [mem_ratPts_iff, mem_ratPts_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨L * k * B, by rw [hfor, ← hk, Matrix.map_mul, Matrix.map_mul]⟩
    · rintro ⟨k, hk⟩
      exact ⟨X * L₁ + B * k * L, by
        rw [hback, ← hk, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul,
          Matrix.map_mul]⟩

end GlobalTheory.StabiliserOfVector
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsComplementFrameCompatibleStabilizerEmbeddi
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.StabFrameCompat

theorem exists_factor {P Q P' Q' : ℕ} (hc : P' + Q' + 1 = P + Q) {x : Fin P ⊕ Fin Q → ℂ}
    (hx : star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x ≠ 0)
    {C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ}
    (h1 : Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q')
    (h2 : (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0) {m : Type} [Fintype m]
    (Y : Matrix (Fin P ⊕ Fin Q) m ℂ) (hY : (Yᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0) :
    ∃ U : Matrix (Fin P' ⊕ Fin Q') m ℂ, Y = C * U := by
  obtain ⟨N, -, -, hN, -⟩ := GlobalTheory.UnfoldingCompare.exists_frame_inv hc hx h1 h2
  set X : Matrix (Fin P ⊕ Fin Q) Unit ℂ := replicateCol Unit x with hX
  have e : Y = C * (N * Y).toRows₁ + X * (N * Y).toRows₂ := by
    rw [← fromCols_mul_fromRows, fromRows_toRows, ← Matrix.mul_assoc, hN, Matrix.one_mul]
  set U := (N * Y).toRows₁
  set V := (N * Y).toRows₂
  refine ⟨U, ?_⟩
  have hV : V = 0 := by
    have h3 : (Yᴴ * Formalism.UG.Jpq P Q) *ᵥ x
        = Uᴴ *ᵥ ((Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x) + Vᴴ *ᵥ ((Xᴴ * Formalism.UG.Jpq P Q) *ᵥ x) := by
      conv_lhs => rw [e]
      rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul, Matrix.add_mul, add_mulVec,
        Matrix.mul_assoc, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec x Vᴴ]
    rw [hY, h2, mulVec_zero, zero_add] at h3
    have h4 : ((Xᴴ * Formalism.UG.Jpq P Q) *ᵥ x) () = star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x := by
      rw [← mulVec_mulVec]
      rfl
    ext u i
    have h5 := congrFun h3 i
    rw [Pi.zero_apply, mulVec, dotProduct, Fintype.sum_unique] at h5
    have h6 : star (V () i) * (star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x) = 0 := by
      rw [← h4]; exact h5.symm
    rcases mul_eq_zero.1 h6 with h | h
    · simpa using h
    · exact absurd h hx
  rw [hV, Matrix.mul_zero, add_zero] at e
  exact e

theorem exists_compatible_frame : ∀ (P Q P' Q' M M' : ℕ), P' + Q' + 1 = P + Q → M' = P' + Q' → ∀ (G : Matrix (Fin M) (Fin M) ℂ) (G' : Matrix (Fin M') (Fin M') ℂ) (B : Matrix (Fin M) (Fin M') ℂ) (x : Fin M → ℂ) (A : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ), Aᴴ * Formalism.UG.Jpq P Q * A = G → Bᴴ * G * B = G' → G'.det ≠ 0 → (Bᴴ * G) *ᵥ x = 0 → star (A *ᵥ x) ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ (A *ᵥ x) ≠ 0 → ∀ j : UpqT P' Q' →* UpqT P Q, IsStabEmb (A *ᵥ x) j → ∃ A' : Matrix (Fin P' ⊕ Fin Q') (Fin M') ℂ, A'ᴴ * Formalism.UG.Jpq P' Q' * A' = G' ∧ ∀ (g : Matrix (Fin M) (Fin M) ℂ) (g' : Matrix (Fin M') (Fin M') ℂ) (t : UpqT P Q) (t' : UpqT P' Q'), g *ᵥ x = x → g * B = B * g' → UpqT.mat t * A = A * g → UpqT.mat t' * A' = A' * g' → t = j t' := by
  intro P Q P' Q' M M' hc hM G G' B x A hA hB hdet hBx hx j hj
  obtain ⟨C, h1, h2, h3⟩ := hj
  have hY : ((A * B)ᴴ * Formalism.UG.Jpq P Q) *ᵥ (A *ᵥ x) = 0 := by
    rw [mulVec_mulVec, conjTranspose_mul, ← hBx, ← hA]
    simp only [Matrix.mul_assoc]
  obtain ⟨A', hA'⟩ := exists_factor hc hx h1 h2 (A * B) hY
  have hG : A'ᴴ * Formalism.UG.Jpq P' Q' * A' = G' := by
    have : (C * A')ᴴ * Formalism.UG.Jpq P Q * (C * A') = G' := by
      rw [← hA', ← hB, ← hA, conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [← this, ← h1, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  refine ⟨A', hG, ?_⟩
  intro g g' t t' hg hgB ht ht'
  have hl : (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q') * A' = 1 := by
    have := Matrix.nonsing_inv_mul G' (Ne.isUnit hdet)
    rw [← this]
    conv_rhs => arg 2; rw [← hG]
    simp only [Matrix.mul_assoc]
  have e : Fin M' ≃ Fin P' ⊕ Fin Q' := (finCongr hM).trans finSumFinEquiv.symm
  have hr : A' * (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q') = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv e).1 hl
  refine GlobalTheory.UnfoldingCompare.eq_of_frame hc hx h1 h2 ?_ ?_
  · have k : UpqT.mat t * C * A' = UpqT.mat (j t') * C * A' := by
      rw [(h3 t').2, Matrix.mul_assoc, Matrix.mul_assoc, ← hA', ht', ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, ← hA', ht, Matrix.mul_assoc, hgB, Matrix.mul_assoc]
    calc UpqT.mat t * C = UpqT.mat t * C * (A' * (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q')) := by
          rw [hr, Matrix.mul_one]
      _ = UpqT.mat (j t') * C * (A' * (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q')) := by
          rw [← Matrix.mul_assoc _ A', k, Matrix.mul_assoc _ A']
      _ = _ := by rw [hr, Matrix.mul_one]
  · rw [(h3 t').1, mulVec_mulVec, ht, ← mulVec_mulVec, hg]

end GlobalTheory.StabFrameCompat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormKappaSqMulDetSplitPrime
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomN

theorem norm_kappa_sq_mul_norm_det : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]), ∀ u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ‖ι B.kappa‖ ^ 2 * ‖ι (LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))‖ = 1 := by
  intro D cc δ B hcc hδ q _ hq2 hsplit hcop ι u hu h1 h2 h3
  obtain ⟨γ, hγ, hdet⟩ := _root_.GlobalTheory.KapIsom.main D cc δ B hcc hδ q hq2 hsplit hcop ι u hu h1 h2 h3
  rw [hdet]
  exact _root_.GlobalTheory.KapVal.norm_kappa_sq_mul_det D B.γ₀ γ B.kc q hq2 hsplit hγ ι

end GlobalTheory.MomN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabSelfDualLatticeTransitiveOnLength
section
namespace GlobalTheory.StabOrbit

theorem stabTransitive : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive :=
  GlobalTheory.Proof.SelfDualStabilizer.stabTransitive_iff.1 (stabTransitive_of_lemmas _root_.GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas)

end GlobalTheory.StabOrbit
end

