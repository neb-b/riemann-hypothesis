module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0003
public import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.Bundle0002
public import Formalism.GaussJetBounds.GaussJetProofs.OrbMul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.JetTdegEqDegree
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeries
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0094
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicUnitarySplitPlaceComponent
section
noncomputable section

namespace GlobalTheory.SplitLift

section General

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

open Formalism.UG

omit [Fintype n] [DecidableEq n] in
theorem conjTransposeBy_ringInvolution_add (σ : A →+* A) (M N : Matrix n n A) : cT σ (M + N) = cT σ M + cT σ N := by
  ext i j; simp [cT]

omit [Fintype n] [DecidableEq n] in
theorem conjTransposeBy_ringInvolution_smul (σ : A →+* A) (a : A) (M : Matrix n n A) : cT σ (a • M) = σ a • cT σ M := by
  ext i j; simp [cT]

omit [Fintype n] [DecidableEq n] in
theorem conjTransposeBy_ringInvolution_involutive (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (M : Matrix n n A) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, hσ]

theorem exists_unitary (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (J K : Matrix n n A) (hJ : cT σ J = J)
    (hJK : J * K = 1) (e : A) (he : e * e = e) (he' : e * σ e = 0) (m m' : Matrix n n A)
    (h : e • (m * m') = e • (1 : Matrix n n A)) :
    ∃ g ∈ UJ σ J, (e + σ e) • ((g : Matrix n n A) - 1) = (g : Matrix n n A) - 1 ∧
      e • (g : Matrix n n A) = e • m := by
  have hKJ : K * J = 1 := mul_eq_one_comm.1 hJK
  have hK : cT σ K = K := by
    have h1 : cT σ K * J = 1 := by rw [← hJ, ← cT_mul, hJK, cT_one]
    calc cT σ K = cT σ K * (J * K) := by rw [hJK, mul_one]
      _ = K := by rw [← mul_assoc, h1, one_mul]
  have hee : σ e * σ e = σ e := by rw [← map_mul, he]
  have he'' : σ e * e = 0 := by rw [mul_comm, he']

  obtain ⟨x, hx⟩ : ∃ x, x = m - 1 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = m' - 1 := ⟨_, rfl⟩
  have hm : m = 1 + x := by rw [hx]; abel
  have hm' : m' = 1 + y := by rw [hy]; abel
  have hab : (1 + e • x) * (1 + e • y) = 1 := by
    have h2 : e • (x + y + x * y) = 0 := by
      have : x + y + x * y = m * m' - 1 := by rw [hm, hm']; noncomm_ring
      rw [this, smul_sub, h, sub_self]
    calc (1 + e • x) * (1 + e • y) = 1 + (e • x + e • y + (e • x) * (e • y)) := by
          simp only [mul_add, add_mul, one_mul, mul_one]; abel
      _ = 1 := by
        rw [smul_mul_smul_comm, he, ← smul_add, ← smul_add, h2, add_zero]
  have hba : (1 + e • y) * (1 + e • x) = 1 := mul_eq_one_comm.1 hab
  let s : Matrix n n A → Matrix n n A := fun z => K * cT σ z * J
  have hs_mul : ∀ z w, s (z * w) = s w * s z := by
    intro z w
    show K * cT σ (z * w) * J = K * cT σ w * J * (K * cT σ z * J)
    rw [cT_mul]
    calc K * (cT σ w * cT σ z) * J = K * cT σ w * (J * K) * cT σ z * J := by rw [hJK]; noncomm_ring
      _ = _ := by noncomm_ring
  have hs_one : s 1 = 1 := by
    show K * cT σ 1 * J = 1
    rw [cT_one, mul_one, hKJ]
  have hs_e : ∀ z, s (1 + e • z) = 1 + σ e • s z := by
    intro z
    show K * cT σ (1 + e • z) * J = 1 + σ e • (K * cT σ z * J)
    rw [conjTransposeBy_ringInvolution_add, cT_one, conjTransposeBy_ringInvolution_smul, mul_add, add_mul, mul_one, hKJ, Matrix.mul_smul, Matrix.smul_mul]
  have hss : ∀ z, s (s z) = z := by
    intro z
    show K * cT σ (K * cT σ z * J) * J = z
    rw [cT_mul, cT_mul, conjTransposeBy_ringInvolution_involutive σ hσ, hJ, hK]
    calc K * (J * (z * K)) * J = (K * J) * z * (K * J) := by noncomm_ring
      _ = z := by rw [hKJ, one_mul, mul_one]
  have hcomm : ∀ z w : Matrix n n A, (1 + e • z) * (1 + σ e • w) = 1 + e • z + σ e • w ∧
      (1 + σ e • w) * (1 + e • z) = 1 + e • z + σ e • w := by
    intro z w
    constructor
    · rw [mul_add, add_mul, add_mul, smul_mul_smul_comm e z (σ e) w, he', zero_smul]; simp
    · rw [mul_add, add_mul, add_mul, smul_mul_smul_comm (σ e) w e z, he'', zero_smul]; simp; abel
  have hu : s ((1 + e • x) * s (1 + e • y)) * ((1 + e • x) * s (1 + e • y)) = 1 := by
    have hc : s (1 + e • x) * (1 + e • x) = (1 + e • x) * s (1 + e • x) := by
      rw [hs_e, (hcomm _ _).1, (hcomm _ _).2]
    rw [hs_mul, hss]
    calc (1 + e • y) * s (1 + e • x) * ((1 + e • x) * s (1 + e • y))
        = (1 + e • y) * (s (1 + e • x) * (1 + e • x)) * s (1 + e • y) := by simp only [mul_assoc]
      _ = ((1 + e • y) * (1 + e • x)) * (s (1 + e • x) * s (1 + e • y)) := by rw [hc]; simp only [mul_assoc]
      _ = 1 := by rw [← hs_mul, hba, hs_one, one_mul]
  have hg : (1 + e • x) * s (1 + e • y) = 1 + e • x + σ e • s y := by rw [hs_e, (hcomm _ _).1]
  refine ⟨⟨_, _, mul_eq_one_comm.1 hu, hu⟩, ?_, ?_, ?_⟩
  · show cT σ ((1 + e • x) * s (1 + e • y)) * J * ((1 + e • x) * s (1 + e • y)) = J
    generalize (1 + e • x) * s (1 + e • y) = g at hu
    calc cT σ g * J * g = (J * K) * (cT σ g * J * g) := by rw [hJK, one_mul]
      _ = J * (s g * g) := by simp only [s, mul_assoc]
      _ = J := by rw [hu, mul_one]
  · show (e + σ e) • ((1 + e • x) * s (1 + e • y) - 1) = (1 + e • x) * s (1 + e • y) - 1
    have : (1 + e • x) * s (1 + e • y) - 1 = e • x + σ e • s y := by rw [hg]; abel
    rw [this, smul_add, smul_smul, smul_smul, add_mul, add_mul, he, he', he'', hee, add_zero, zero_add]
  · show e • ((1 + e • x) * s (1 + e • y)) = e • m
    rw [hg, hm, smul_add, smul_add, smul_add, smul_smul, smul_smul, he, he', zero_smul, add_zero]

theorem exists_unitary_prod {B C : Type} [CommRing B] [CommRing C] (p : A →+* B) (q : A →+* C) (φ : A ≃+* B × C)
    (hφ : ∀ z, (φ z).1 = p z ∧ (φ z).2 = q z)
    (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (J K : Matrix n n A) (hJ : cT σ J = J)
    (hJK : J * K = 1) (e : A) (he : e * e = e) (he' : e * σ e = 0) (hinf : p e = 0) (m m' : Matrix n n C)
    (h : q e • (m * m') = q e • (1 : Matrix n n C)) :
    ∃ g ∈ UJ σ J, (∀ i j, (e + σ e) * ((g : Matrix n n A) - 1) i j = ((g : Matrix n n A) - 1) i j) ∧
      q e • (g : Matrix n n A).map q = q e • m := by
  have lift : ∀ M : Matrix n n C, ∃ N : Matrix n n A, N.map q = M := by
    intro M
    refine ⟨Matrix.of fun i j => φ.symm (0, M i j), Matrix.ext fun i j => ?_⟩
    show q (φ.symm (0, M i j)) = M i j
    rw [← (hφ _).2, RingEquiv.apply_symm_apply]
  obtain ⟨N, rfl⟩ := lift m
  obtain ⟨N', rfl⟩ := lift m'
  have hN : e • (N * N') = e • (1 : Matrix n n A) := by
    refine Matrix.ext fun i j => φ.injective (Prod.ext ?_ ?_)
    · rw [(hφ _).1, (hφ _).1, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
        map_mul, map_mul, hinf, zero_mul, zero_mul]
    · rw [← Matrix.map_mul, ← Matrix.map_one q (map_zero _) (map_one _)] at h
      rw [(hφ _).2, (hφ _).2, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
        map_mul, map_mul]
      exact congrFun (congrFun h i) j
  obtain ⟨g, hg, h1, h2⟩ := exists_unitary σ hσ _ _ hJ hJK e he he' N N' hN
  refine ⟨g, hg, fun i j => congrFun (congrFun h1 i) j, Matrix.ext fun i j => ?_⟩
  have h3 : e * g.1 i j = e * N i j := congrFun (congrFun h2 i) j
  have h4 := congrArg q h3
  rw [map_mul, map_mul] at h4
  exact h4

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem split_lift : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ m m' : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), finPart D e • (m * m') = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) → ∃ g : GA D V, Formalism.L2.Theta.SuppAt e V g ∧ finPart D e • finMat D.sp.cm.sig V.gram g = finPart D e • m := by
  intro D V e he m m' h
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hφ' : ∀ z, (φ z).1 = infPart D z ∧ (φ z).2 = finPart D z := hφ
  have hinf : infPart D e = 0 := by
    obtain ⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h4⟩ := he
    have h5 : infPart D (e + cA D e) = 0 := by
      rw [h4]
      exact TensorProduct.zero_tmul _ _
    have h6 : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
    rw [h6, RingHom.map_mul, h5, mul_zero]
  have hJK : JR (AF D.host.F) V.gram * (V.gram⁻¹).map (incA D) = 1 := by
    show V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.UnitaryGlue.gram_det_ne_zero V).isUnit,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT (cA D) (JR (AF D.host.F) V.gram) = JR (AF D.host.F) V.gram := by
    refine Matrix.ext fun i j => ?_
    show cA D (incA D (V.gram j i)) = incA D (V.gram i j)
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  obtain ⟨g, hg, h1, h2⟩ := exists_unitary_prod (infPart D) (finPart D) φ hφ' (cA D) GlobalTheory.DualPairCheck.cA_cA _ _
    hJ hJK e he.1 he.2.1 hinf m m' h
  exact ⟨⟨g, hg⟩, h1, h2⟩

end GlobalTheory.SplitLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitOnto

section Generic

variable {A : Type} [CommRing A] {n : ℕ}

def adj (c : A →+* A) (G H X : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A := H * (X.map c)ᵀ * G

variable {c : A →+* A} {G H : Matrix (Fin n) (Fin n) A}

theorem adj_add (X Y : Matrix (Fin n) (Fin n) A) : adj c G H (X + Y) = adj c G H X + adj c G H Y := by
  simp only [adj, Matrix.map_add _ (map_add c), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem adj_smul (a : A) (X : Matrix (Fin n) (Fin n) A) : adj c G H (a • X) = c a • adj c G H X := by
  have : (a • X).map c = c a • X.map c := by
    ext i j
    simp
  simp only [adj, this, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem adj_one (h : G * H = 1) : adj c G H 1 = 1 := by
  rw [adj, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one, mul_eq_one_comm.1 h]

theorem adj_mul (h : G * H = 1) (X Y : Matrix (Fin n) (Fin n) A) :
    adj c G H (X * Y) = adj c G H Y * adj c G H X := by
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc G H, h, Matrix.one_mul]

theorem adj_adj (hc : ∀ a, c (c a) = a) (h : G * H = 1) (hG : (G.map c)ᵀ = G) (X : Matrix (Fin n) (Fin n) A) :
    adj c G H (adj c G H X) = X := by
  have h' : H * G = 1 := mul_eq_one_comm.1 h
  have h1 : (H.map c)ᵀ * G = 1 := by
    conv_lhs => rw [← hG]
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one]
  have h2 : (((X.map c)ᵀ).map c)ᵀ = X := by
    ext i j
    exact hc _
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul, h2, hG, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [← Matrix.mul_assoc, h', Matrix.one_mul]

theorem exists_unitary (hc : ∀ a, c (c a) = a) (h : G * H = 1) (hG : (G.map c)ᵀ = G) {e : A} (he : e * e = e)
    (he' : e * c e = 0) (M M' : Matrix (Fin n) (Fin n) A) (hM : e • (M' * M) = e • (1 : Matrix (Fin n) (Fin n) A)) :
    ∃ g : GL (Fin n) A, (g.1.map c)ᵀ * G * g.1 = G ∧ (e + c e) • (g.1 - 1) = g.1 - 1 ∧ e • g.1 = e • M := by
  have hee : c e * c e = c e := by rw [← map_mul, he]
  have he2 : c e * e = 0 := by rw [mul_comm, he']
  set f := 1 - e - c e with hf
  have hcf : c f = f := by rw [hf, map_sub, map_sub, map_one, hc]; ring
  have h1 : e * f = 0 := by rw [hf]; linear_combination -he - he'
  have h2 : c e * f = 0 := by rw [hf]; linear_combination -hee - he'
  have h3 : f * e = 0 := by rw [mul_comm, h1]
  have h4 : f * c e = 0 := by rw [mul_comm, h2]
  have h5 : f * f = f := by linear_combination f * hf - h3 - h4
  set g := e • M + c e • adj c G H M' + f • (1 : Matrix (Fin n) (Fin n) A) with hg
  have hadj : adj c G H g = e • M' + c e • adj c G H M + f • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [hg, adj_add, adj_add, adj_smul, adj_smul, adj_smul, adj_adj hc h hG, adj_one h, hc, hcf, add_comm (c e • _)]
  have hM' : c e • (adj c G H M * adj c G H M') = c e • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [← adj_mul h, ← adj_smul, hM, adj_smul, adj_one h]
  have hinv : adj c G H g * g = 1 := by
    rw [hadj, hg]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, he, he', hee, he2,
      h1, h2, h3, h4, h5, zero_smul, add_zero, zero_add, Matrix.mul_one, hM, hM']
    rw [← add_smul, ← add_smul, hf]
    simp
  refine ⟨⟨g, adj c G H g, mul_eq_one_comm.1 hinv, hinv⟩, ?_, ?_, ?_⟩
  · change (g.map c)ᵀ * G * g = G
    have := congrArg (G * ·) hinv
    simpa only [adj, ← Matrix.mul_assoc, h, Matrix.one_mul, Matrix.mul_one] using this
  · change (e + c e) • (g - 1) = g - 1
    have h6 : f • g = f • (1 : Matrix (Fin n) (Fin n) A) := by
      simp only [hg, smul_add, smul_smul, h3, h4, h5, zero_smul, zero_add]
    have h7 : e + c e = 1 - f := by rw [hf]; ring
    rw [h7, sub_smul, one_smul, smul_sub, h6, sub_self, sub_zero]
  · change e • g = e • M
    simp only [hg, smul_add, smul_smul, he, he', h1, zero_smul, add_zero]

end Generic

variable {D : D7}

theorem cA_cA (z : Formalism.L2.Theta.AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (star_star x)
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

theorem gram_det_ne (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    have hx : x = ∑ i, V.frame.repr x i • V.frame i := (V.frame.sum_repr x).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : ∑ j, V.gram i j * v j = 0 := congr_fun h0 i
    have h2 : V.hT (V.frame i) (V.frame.equivFun.symm v) = ∑ j, V.gram i j * v j := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Module.Basis.equivFun_symm_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]; rfl
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h2, h1, smul_zero]
  exact V.frame.equivFun.symm.injective (this.trans (map_zero _).symm)

theorem gram_mul_inv (V : HSp D) : V.gram.map (incA D) * V.gram⁻¹.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem gram_conj (V : HSp D) : ((V.gram.map (incA D)).map (cA D))ᵀ = V.gram.map (incA D) := by
  ext i j
  have h : star (V.gram j i) = V.gram i j := LinearMap.isSymm_def.1 V.herm _ _
  exact congrArg (incA D) h

theorem exists_suppAt_rho_eq : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β x : GL (Fin V.rank) (Fv D.host.F v)), ∃ g : GA D V, SuppAt e V g ∧ rho V π β g = x := by
  intro D e v π he hπ V β x
  obtain ⟨he1, he2, -⟩ := he
  obtain ⟨hs, hk, -, -⟩ := hπ
  have key : ∀ a b, π a = π b ↔ e * a = e * b := fun a b => by
    rw [← sub_eq_zero, ← map_sub, hk, mul_sub, sub_eq_zero]
  have keyM : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (AE D), X.map π = Y.map π ↔ e • X = e • Y := fun X Y => by
    simp only [← Matrix.ext_iff, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, key]
  have lift : ∀ Z : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v),
      ∃ X : Matrix (Fin V.rank) (Fin V.rank) (AE D), X.map π = Z := fun Z => by
    choose X hX using fun i j => hs (Z i j)
    exact ⟨Matrix.of X, Matrix.ext hX⟩
  obtain ⟨M, hM⟩ := lift (β * x * β⁻¹).1
  obtain ⟨M', hM'⟩ := lift ((β * x * β⁻¹)⁻¹).1
  obtain ⟨g, h1, h2, h3⟩ := exists_unitary (c := cA D) cA_cA (gram_mul_inv V) (gram_conj V) he1 he2 M M' (by
    rw [← keyM, Matrix.map_mul, hM, hM', Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  let g' : HR (AF D.host.F) D.sp.cm.sig V.gram := ⟨g, h1⟩
  refine ⟨g', fun i j => congrFun (congrFun h2 i) j, Units.ext ?_⟩
  refine (rho_val V π β g').trans ?_
  change (β⁻¹).1 * g.1.map π * β.1 = x.1
  rw [(keyM _ _).2 h3, hM, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group

end GlobalTheory.SplitOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExpFactorAllOrbitsEqProdOrbits
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)

namespace GlobalTheory.ExpFacOrbits

theorem expFactor_allOrbits : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (R : Finset (OrbitPlaces.Pl D)) {M N N' : ℕ} (eA : Fin M ≃ R × Fin N)
    (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (hbe : constantCoeff be = 0), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (mvExp ((-1 : ℂ_[p]) • Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be)) =
      product_zeroth_first_parts.expS ℂ_[p] (OrbitPlaces.beAll D p (N0 := N) (N1 := N') R (fun _ => -1) (fun _ => be)) := by
  intro D p _ R M N N' eA be hbe
  classical
  set a : ZV (nP D p) M N' → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] := fun y =>
    X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) with ha_def
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero (fun y => constantCoeff_X _)
  have hlin : ∀ ab : Fin M × Fin N', (fun s : ZMod (nP D p) =>
      Formalism.DworkPowerSeriesWeights.linSub (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) (s, ab.1, ab.2)) =
      fun s => (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p]) := fun ab =>
    funext fun s => Formalism.DworkPowerSeriesWeights.OrbMul.linSub_idM (s, ab.1, ab.2)
  have hX : ∀ ab : Fin M × Fin N', HasSubst (fun s : ZMod (nP D p) =>
      (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p])) := fun ab =>
    hasSubst_of_constantCoeff_zero (fun s => constantCoeff_X _)
  have hB : Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be =
      ∑ ab : Fin M × Fin N', subst (fun s : ZMod (nP D p) =>
        (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p])) be := by
    unfold Formalism.DworkPowerSeriesWeights.bSum
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [hlin ab]
  have hcc : constantCoeff ((-1 : ℂ_[p]) •
      Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hB, Finset.smul_sum, map_sum]
    refine Finset.sum_eq_zero fun ab _ => ?_
    rw [MvPowerSeries.constantCoeff_smul, constantCoeff_subst_eq_zero (hX ab) (fun s => constantCoeff_X _) hbe,
      smul_zero]
  rw [Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' ha hcc]
  show mvExp _ = mvExp _
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hB, ← coe_substAlgHom ha, map_smul, map_sum, coe_substAlgHom ha]
  have hterm : ∀ ab : Fin M × Fin N', subst a (subst (fun s : ZMod (nP D p) =>
        (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p])) be) =
      subst (fun s : ZMod (nP D p) =>
        (X (OrbitPlaces.orbMap D p (eA ab.1).1 s, (eA ab.1).2, ab.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) be := by
    intro ab
    rw [subst_comp_subst_apply (hX ab) ha]
    congr 1
    funext s
    rw [subst_X ha]
  simp_rw [hterm]
  unfold OrbitPlaces.beAll
  simp only [← Finset.smul_sum]
  congr 1
  rw [Fintype.sum_prod_type]
  rw [Equiv.sum_comp eA (fun x : R × Fin N => ∑ b : Fin N', subst (fun s : ZMod (nP D p) =>
        (X (OrbitPlaces.orbMap D p x.1 s, x.2, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) be)]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_coe_sort R (fun r => ∑ a : Fin N, ∑ b : Fin N', subst (fun s : ZMod (nP D p) =>
        (X (OrbitPlaces.orbMap D p r s, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) be)

end GlobalTheory.ExpFacOrbits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankReductionRangeAddCorank
section
open Matrix

namespace GlobalTheory.SplitHecke

theorem finrank_range_reduction (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] (p : O) (hp : Irreducible p) (n j : ℕ) (a : GL (Fin n) K)
    (A : Matrix (Fin n) (Fin n) O) (hj : j ≤ n) (h : Hk O p j a) (hA : A.map (algebraMap O K) = a.1) :
    Module.finrank (IsLocalRing.ResidueField O)
      (LinearMap.range (A.map (IsLocalRing.residue O)).mulVecLin) + j = n := by
  classical
  obtain ⟨-, h2, u, hu⟩ := h
  obtain ⟨B, hB⟩ := intM_iff.1 h2
  have inj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hAB : A * B = p • (1 : Matrix (Fin n) (Fin n) O) := by
    apply Matrix.map_injective inj
    change (A * B).map (algebraMap O K) = (p • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O K)
    rw [Matrix.map_mul, hA, hB, Matrix.mul_smul, Units.mul_inv]
    ext i k
    by_cases e : i = k <;> simp [e]
  have hdet : Associated A.det (p ^ j) := by
    have : A.det = p ^ j * u := by
      apply inj
      rw [← hu, ← hA, RingHom.map_det]
      rfl
    rw [this]
    exact (associated_mul_unit_left _ _ u.isUnit)
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := GlobalTheory.SmithBetween.smith_between O p hp n j hj A B hAB hdet
  set r := IsLocalRing.residue O with hr
  have hP' : IsUnit (P.map r).det := by
    have := hP.map r
    rwa [RingHom.map_det] at this
  have hQ' : IsUnit (Q.map r).det := by
    have := hQ.map r
    rwa [RingHom.map_det] at this
  have hp0 : r p = 0 := (IsLocalRing.residue_eq_zero_iff p).2 hp.not_isUnit
  have h3 : A.map r * Q.map r = P.map r *
      Matrix.diagonal (fun i : Fin n => if i.1 < n - j then (1 : IsLocalRing.ResidueField O) else 0) := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_mul, Matrix.diagonal_map (map_zero r)]
    congr 2
    funext i
    split_ifs <;> simp [hp0]
  have h4 := congrArg Matrix.rank h3
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQ', Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP',
    Matrix.rank_diagonal] at h4
  have h5 : Fintype.card {i : Fin n // (if i.1 < n - j then (1 : IsLocalRing.ResidueField O) else 0) ≠ 0}
      = n - j := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun i : Fin n =>
        (if i.1 < n - j then (1 : IsLocalRing.ResidueField O) else 0) ≠ 0)
        = Finset.univ.filter fun i : Fin n => i.1 < n - j := by
      ext i
      by_cases e : i.1 < n - j <;> simp only [Finset.mem_filter, Finset.mem_univ, e, if_true, if_false, true_and, ne_eq, one_ne_zero, not_false_eq_true, not_true_eq_false]
    rw [this, Fin.card_filter_val_lt]
    omega
  have h6 : (A.map r).rank = n - j := by
    rw [h4]
    convert h5
  change (A.map r).rank + j = n
  omega

end GlobalTheory.SplitHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizationUnimodularCompanionEqStatement
section
open NumberField Formalism.BasicNotions Formalism.L2.PairingIndexBounds.F

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_unimodularCompanion_eq : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Q : Ideal (𝓞 E)) (Λ Λ₁ : Submodule (𝓞 E) (Fin N → E)), Λ.FG → Λ₁.FG → Formalism.HermitianLatticesTheory.loc (K := E) Q Λ = Formalism.HermitianLatticesTheory.loc (K := E) Q Λ₁ → Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ) = Formalism.HermitianLatticesTheory.loc (K := E) Q (compan (sp := sp) J a Λ₁) := by
  first | exact @GlobalTheory.loc_compan_eq | exact GlobalTheory.loc_compan_eq | (intros; apply GlobalTheory.loc_compan_eq <;> assumption)
end

