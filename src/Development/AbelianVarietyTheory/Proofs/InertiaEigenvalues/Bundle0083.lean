module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RealInducedCharacters.Induced

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermBasisOrthonormal
section
noncomputable section

namespace GlobalTheory.UnitLemma.OrthBasis

open GlobalTheory.UnitLemma

variable {K : UQ} (B : InvAlg K)

theorem herm_add_right (x y z₁ z₂ : B.A) : B.herm x y (z₁ + z₂) = B.herm x y z₁ + B.herm x y z₂ := by
  unfold InvAlg.herm
  rw [map_add (f := _), mul_add, map_add (f := _)]

theorem herm_zero_right (x y : B.A) : B.herm x y 0 = 0 := by
  unfold InvAlg.herm
  simp

theorem herm_smul_right' (x y z : B.A) (a : K.E) : B.herm x y (a • z) = K.c a * B.herm x y z := by
  unfold InvAlg.herm
  rw [Algebra.smul_def, map_mul B.σ, B.σ_alg, ← Algebra.smul_def, mul_smul_comm, map_smul, smul_eq_mul]

theorem herm_sum_smul_left {n : ℕ} (x z : B.A) (a : Fin n → K.E) (v : Fin n → B.A) :
    B.herm x (∑ j, a j • v j) z = ∑ j, a j * B.herm x (v j) z := by
  unfold InvAlg.herm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]

theorem herm_mul_left_of_fixed (x g y z : B.A) (hg : B.σ g = g) :
    B.herm x (g * y) z = B.herm x y (g * z) := by
  unfold InvAlg.herm
  rw [map_mul B.σ, hg]; congr 1; ring

theorem repr_mul {n : ℕ} (e : Module.Basis (Fin n) K.E B.A) (g z : B.A) (i : Fin n) :
    e.repr (g * z) i = ∑ j, e.repr z j * e.repr (g * e j) i := by
  conv_lhs => rw [← e.sum_repr z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, map_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

end GlobalTheory.UnitLemma.OrthBasis

namespace GlobalTheory.UnitLemma

open GlobalTheory.UnitLemma.OrthBasis

theorem herm_basis_orthonormal : ∀ (K : UQ) (B : InvAlg K) (x w : B.A), B.σ B.g = B.g → IsUnit w →
    Submodule.span K.E (Set.range fun l : ℕ => B.g ^ l) = ⊤ → ∀ (n : ℕ) (e : Module.Basis (Fin n) K.E B.A),
    (∀ i j, K.c (e.repr (B.g * e j) i) = e.repr (B.g * e i) j) → (∀ j, B.herm x (e j) w = K.c (e.repr w j)) →
    ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0 := by
  intro K B x w hg hw hspan n e hM hwj

  let P : B.A → Prop := fun z => ∀ i, B.herm x (e i) z = K.c (e.repr z i)
  have hstep : ∀ z, P z → P (B.g * z) := by
    intro z hz i
    rw [← herm_mul_left_of_fixed B x B.g (e i) z hg]
    conv_lhs => rw [← e.sum_repr (B.g * e i)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [herm_sum_smul_left, repr_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hz j, RingEquiv.map_mul K.c, hM, mul_comm]
  have hpow : ∀ l : ℕ, P (B.g ^ l * w) := by
    intro l
    induction l with
    | zero => simpa [P] using hwj
    | succ l ih => rw [pow_succ', mul_assoc]; exact hstep _ ih
  have hspanP : ∀ a ∈ Submodule.span K.E (Set.range fun l : ℕ => B.g ^ l), P (a * w) := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem y hy => obtain ⟨l, rfl⟩ := hy; exact hpow l
    | zero => intro i; simp [herm_zero_right]
    | add y z _ _ hy hz =>
      intro i; rw [add_mul, herm_add_right, hy i, hz i, map_add (f := _), Finsupp.add_apply, map_add (f := _)]
    | smul a y _ hy =>
      intro i; rw [smul_mul_assoc, herm_smul_right', hy i, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul,
        RingEquiv.map_mul K.c]
  have hall : ∀ z, P z := by
    intro z
    obtain ⟨u, rfl⟩ := hw
    have := hspanP (z * ((u⁻¹ : B.Aˣ) : B.A)) (by rw [hspan]; exact Submodule.mem_top)
    rwa [mul_assoc, Units.inv_mul, mul_one] at this
  intro i j
  rw [hall (e j) i, e.repr_self, Finsupp.single_apply]
  split_ifs with h1 h2 h2
  · exact map_one _
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · exact map_zero _

end GlobalTheory.UnitLemma
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianBlockHasInvariantsOfLiftMatch
section
open GlobalTheory.JR Matrix

noncomputable section

namespace GlobalTheory.JR.Step

section MapLemmas
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k')

theorem mom_glMap (Y : Gl r k) (i : ℕ) : mom (glMap φ Y) i = φ (mom Y i) := by
  simp only [mom, glMap]
  rw [RingHom.map_dotProduct, ← Matrix.map_pow]
  congr 1
  ext j
  simp [RingHom.map_mulVec]
  rfl

theorem inv_glMap (Y : Gl r k) : inv (glMap φ Y) = (inv Y).map φ := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i
    simp [inv, Inv.map, glMap, Matrix.charpoly_map]
  · ext i
    simp only [inv, Inv.map]
    exact mom_glMap φ Y i
  · rfl

theorem sec_map (a : Inv r k) : sec (a.map φ) = glMap φ (sec a) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · ext i j
    simp only [sec, glMap, companion, Inv.map, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  · ext i
    simp only [sec, glMap]
    split_ifs <;> simp
  · rfl
  · rfl

theorem Delta_map (a : Inv r k) : Delta (a.map φ) = φ (Delta a) := by
  have : hankel (a.map φ) = (hankel a).map φ := by
    ext i j
    simp only [hankel, Matrix.of_apply, Matrix.map_apply, sec_map, mom_glMap]
  rw [Delta, Delta, this, RingHom.map_det]
  rfl

theorem full_glMap (Y : Gl r k) : full (glMap φ Y) = (full Y).map φ := by
  ext i j
  simp only [full, glMap, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  rcases (finSumFinEquiv.symm i) with a | a <;> rcases (finSumFinEquiv.symm j) with b | b <;> simp

end MapLemmas

section Blocks
variable {r : ℕ} {k : Type} [CommRing k]

theorem blocks_full (Y : Gl r k) : blocks (full Y) = Y := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · ext i j
    simp [blocks, full, finSumFinEquiv_symm_apply_castSucc]
  · ext i
    simp [blocks, full, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]
  · ext i
    simp [blocks, full, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]
  · simp [blocks, full, finSumFinEquiv_symm_last]

theorem full_injective : Function.Injective (full : Gl r k → _) :=
  Function.LeftInverse.injective blocks_full

theorem full_act (g : GL (Fin r) k) (Y : Gl r k) :
    full (act g Y) = embHom r k g * full Y * embHom r k ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  simp only [full, embHom, act, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  congr 1
  · simp
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply]

theorem det_embHom (h : Matrix (Fin r) (Fin r) k) : (embHom r k h).det = h.det := by
  simp [embHom, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

end Blocks

theorem hasInv_of_lift : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (X : Hn r F E) (μ l : F) (ν : E),
    ν * star ν = algebraMap F E μ → μ ≠ 0 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 →
    HasInv (GlobalTheory.JR.Step.liftH X ν l) (inv (GlobalTheory.JR.Step.lift Z μ l)) → HasInv X (inv Z) := by
  intro F E _ _ _ _ _ r Z X μ l ν hν hμ hΔ hX
  have hφ : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  have hμ' : algebraMap F E μ ≠ 0 := fun h => hμ (hφ (h.trans (map_zero _).symm))
  have hsν : star ν ≠ 0 := by
    intro h; apply hμ'; rw [← hν, h, mul_zero]
  have hinv : inv (liftH X ν l).toGl = inv (glMap (algebraMap F E) (lift Z μ l)) := by
    rw [inv_glMap]; exact hX
  have hD : Delta (inv (glMap (algebraMap F E) (lift Z μ l))) ≠ 0 := by
    rw [inv_glMap, Delta_map]
    exact fun h => hΔ (hφ (h.trans (map_zero _).symm))
  obtain ⟨g, ⟨hg, -⟩, -⟩ := (_root_.GlobalTheory.JR.normalForm_invariants E (r + 1)).2.2.2.2 _ _ hD hinv
  set G : Matrix (Fin (r + 1)) (Fin (r + 1)) E := (g : Matrix (Fin (r + 1)) (Fin (r + 1)) E) with hG
  set Gi : Matrix (Fin (r + 1)) (Fin (r + 1)) E := ((g⁻¹ : GL (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    with hGi
  have hGiG : Gi * G = 1 := by rw [hG, hGi, Units.inv_mul]
  have h1 : G * full (glMap (algebraMap F E) Z) * Gi = full X.toGl := by
    rw [full_glMap]; exact congrArg Prod.fst hg
  have h2 : G *ᵥ (fun i => algebraMap F E ((μ • eL r F) i)) = ν • eL r E := congrArg (fun Y => Y.2.1) hg
  have h3 : (fun i => algebraMap F E (eL r F i)) ᵥ* Gi = star (ν • eL r E) := congrArg (fun Y => Y.2.2.1) hg
  have hv1 : (fun i => algebraMap F E ((μ • eL r F) i)) = algebraMap F E μ • eL r E := by
    ext i; simp only [eL, Pi.smul_apply, Pi.single_apply, smul_eq_mul]; split_ifs <;> simp
  have hv2 : (fun i => algebraMap F E (eL r F i)) = eL r E := by
    ext i; simp only [eL, Pi.single_apply]; split_ifs <;> simp
  have hv3 : star (ν • eL r E) = star ν • eL r E := by
    ext i; simp only [eL, Pi.star_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]; split_ifs <;> simp
  rw [hv1] at h2
  rw [hv2, hv3] at h3
  have hcol : ∀ i, G i (Fin.last r) * algebraMap F E μ = ν * eL r E i := by
    intro i
    have := congrFun h2 i
    rw [Matrix.mulVec_smul, eL, Matrix.mulVec_single_one] at this
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply] at this
    rw [mul_comm]
    exact this
  have hrow : eL r E ᵥ* G = (star ν)⁻¹ • eL r E := by
    have hs : star ν • (eL r E ᵥ* G) = eL r E := by
      rw [← Matrix.smul_vecMul, ← h3, Matrix.vecMul_vecMul, hGiG, Matrix.vecMul_one]
    calc eL r E ᵥ* G = (star ν)⁻¹ • (star ν • (eL r E ᵥ* G)) := by
          rw [smul_smul, inv_mul_cancel₀ hsν, one_smul]
      _ = (star ν)⁻¹ • eL r E := by rw [hs]
  have eLL : G (Fin.last r) (Fin.last r) = (star ν)⁻¹ := by
    have := congrFun hrow (Fin.last r)
    simpa [eL, Matrix.single_one_vecMul] using this
  have eLc : ∀ b : Fin r, G (Fin.last r) (Fin.castSucc b) = 0 := by
    intro b
    have := congrFun hrow (Fin.castSucc b)
    simpa [eL, Matrix.single_one_vecMul, Fin.castSucc_ne_last] using this
  have ecL : ∀ a : Fin r, G (Fin.castSucc a) (Fin.last r) = 0 := by
    intro a
    have := hcol (Fin.castSucc a)
    simp only [eL, Pi.single_apply, Fin.castSucc_ne_last, if_false, mul_zero] at this
    exact (mul_eq_zero.mp this).resolve_right hμ'
  set H : Matrix (Fin (r + 1)) (Fin (r + 1)) E := star ν • G with hH
  set h' : Matrix (Fin r) (Fin r) E := H.submatrix Fin.castSucc Fin.castSucc with hh'
  have hHemb : H = embHom r E h' := by
    ext i j
    refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
    all_goals simp [embHom, H, h', finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last, eLL, eLc, ecL, hsν]
  have hdetG : G.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det G).mp g.isUnit).ne_zero
  have hdet : h'.det ≠ 0 := by
    rw [← det_embHom, ← hHemb, hH, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hsν) hdetG
  set u : GL (Fin r) E := Matrix.GeneralLinearGroup.mkOfDetNeZero h' hdet with hu_def
  have hu : (u : Matrix (Fin r) (Fin r) E) = h' := rfl
  have hGM : G * full (glMap (algebraMap F E) Z) = full X.toGl * G := by
    calc G * full (glMap (algebraMap F E) Z) = G * full (glMap (algebraMap F E) Z) * (Gi * G) := by
          rw [hGiG, Matrix.mul_one]
      _ = (G * full (glMap (algebraMap F E) Z) * Gi) * G := by
          rw [Matrix.mul_assoc (G * full (glMap (algebraMap F E) Z))]
      _ = full X.toGl * G := by rw [h1]
  have hHM : H * full (glMap (algebraMap F E) Z) = full X.toGl * H := by
    rw [hH, Matrix.smul_mul, Matrix.mul_smul, hGM]
  have key : full (act u (glMap (algebraMap F E) Z)) = full X.toGl := by
    rw [full_act, hu, ← hHemb, hHM, hHemb, Matrix.mul_assoc, ← map_mul (embHom r E), ← hu, Units.mul_inv,
      map_one, Matrix.mul_one]
  have hXeq : X.toGl = act u (glMap (algebraMap F E) Z) := (full_injective key).symm
  unfold HasInv
  rw [hXeq, (_root_.GlobalTheory.JR.normalForm_invariants E r).1, inv_glMap]

end GlobalTheory.JR.Step
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianLatticeIsOpenIsCompactTest
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LatTop

theorem isLocallyConstant_indicator_one' {Z : Type} [TopologicalSpace Z] {W : Set Z} (hW : IsClopen W) :
    IsLocallyConstant (W.indicator (1 : Z → ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ W
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem lattice_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)),
    IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} ∧ IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} ∧
      IsTest (Set.indicator {y : A.L | ∀ i, ‖j y i‖ ≤ 1} (1 : A.L → ℂ)) := by
  intro F E _ _ _ _ hU A r j
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  let jF : A.L ≃ₗ[F] (Fin r → E) := j.restrictScalars F
  have hc : Continuous jF := IsModuleTopology.continuous_of_linearMap jF.toLinearMap
  have hcs : Continuous jF.symm := IsModuleTopology.continuous_of_linearMap jF.symm.toLinearMap
  set B : Set E := Metric.closedBall 0 1 with hB
  have hBo : IsOpen B := IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hBc : IsClosed B := Metric.isClosed_closedBall
  have hBk : IsCompact B := isCompact_closedBall 0 1
  set V : Set (Fin r → E) := Set.univ.pi fun _ => B with hV
  have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hBo
  have hVc : IsClosed V := isClosed_set_pi fun _ _ => hBc
  have hVk : IsCompact V := isCompact_univ_pi fun _ => hBk
  have hS : {y : A.L | ∀ i, ‖j y i‖ ≤ 1} = jF ⁻¹' V := by
    ext y
    simp [hV, hB, jF]
  have hS' : jF ⁻¹' V = jF.symm '' V := (jF.toEquiv.image_symm_eq_preimage V).symm
  have hSo : IsOpen {y : A.L | ∀ i, ‖j y i‖ ≤ 1} := hS ▸ hVo.preimage hc
  have hSc : IsClosed {y : A.L | ∀ i, ‖j y i‖ ≤ 1} := hS ▸ hVc.preimage hc
  have hSk : IsCompact {y : A.L | ∀ i, ‖j y i‖ ≤ 1} := by
    rw [hS, hS']; exact hVk.image hcs
  exact ⟨hSo, hSk, isLocallyConstant_indicator_one' ⟨hSc, hSo⟩,
    HasCompactSupport.intro' hSk hSc fun x hx => Set.indicator_of_notMem hx _⟩

end GlobalTheory.JR.LatTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedRepresentationCharacter
section
open GlobalTheory.Published

noncomputable section

namespace GlobalTheory.InertiaEigenvalues

open BrauerSchur

theorem exists_transversal_index {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    ∃ t : Fin H.index → G, (∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j) ∧ ∀ x, ∃ i, (t i)⁻¹ * x ∈ H := by
  classical
  let e : G ⧸ H ≃ Fin H.index := Finite.equivFin (G ⧸ H)
  refine ⟨fun i => (e.symm i).out, fun i j => ?_, fun x => ⟨e (x : G ⧸ H), ?_⟩⟩
  · rw [← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.out_eq', e.symm.injective.eq_iff]
  · rw [← QuotientGroup.eq]
    simp only [Equiv.symm_apply_apply, QuotientGroup.out_eq']

theorem inducedRep_cyclic_trace (G : Type) [Group G] [Fintype G] (H : Subgroup G) (χ : H →* ℂˣ) :
    ∃ (R : Representation ℂ G (Fin H.index → ℂ)) (v : Fin H.index → ℂ),
      (∀ σ : H, R σ v = (χ σ : ℂ) • v) ∧ Submodule.span ℂ (Set.range fun g => R g v) = ⊤ ∧
      ∀ g, LinearMap.trace ℂ (Fin H.index → ℂ) (R g) = GlobalTheory.Published.indFun H (fun x => (χ x : ℂ)) g := by
  classical
  obtain ⟨t, ht, hc⟩ := exists_transversal_index H
  obtain ⟨i0, hi0⟩ := hc 1
  rw [mul_one] at hi0
  have hti0 : t i0 ∈ H := by simpa using H.inv_mem hi0
  have memiff : ∀ (k i : Fin H.index) (a : G), (t i)⁻¹ * a ∈ H → ((t k)⁻¹ * a * t i0 ∈ H ↔ k = i) := by
    intro k i a ha
    rw [← ht k i]
    constructor
    · intro hm
      have e : (t k)⁻¹ * t i = ((t k)⁻¹ * a * t i0) * (t i0)⁻¹ * ((t i)⁻¹ * a)⁻¹ := by group
      rw [e]
      exact H.mul_mem (H.mul_mem hm (H.inv_mem hti0)) (H.inv_mem ha)
    · intro hm
      have e : (t k)⁻¹ * a * t i0 = ((t k)⁻¹ * t i) * ((t i)⁻¹ * a) * t i0 := by group
      rw [e]
      exact H.mul_mem (H.mul_mem hm ha) hti0
  refine ⟨indRep H χ t ht hc, Pi.single i0 1, ?_, ?_, ?_⟩
  · intro σ
    ext k
    show Matrix.toLin' (indMat H χ t (σ : G)) (Pi.single i0 1) k = _
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
    simp only [Matrix.col_apply, indMat, Pi.smul_apply, smul_eq_mul]
    have hσ : (t i0)⁻¹ * (σ : G) ∈ H := H.mul_mem hi0 σ.2
    by_cases hk : k = i0
    · subst hk
      rw [Pi.single_eq_same, mul_one, dot_conj H χ hti0 (σ : G)]
      unfold dot
      rw [dite_eq_left σ.2]
    · rw [Pi.single_eq_of_ne hk, mul_zero]
      unfold dot
      rw [dite_eq_right]
      rw [memiff k i0 _ hσ]
      exact hk
  · rw [eq_top_iff]
    have hsingle : ∀ i, Pi.single i (1 : ℂ) ∈ Submodule.span ℂ (Set.range fun g => indRep H χ t ht hc g (Pi.single i0 1)) := by
      intro i
      have hti : (t i)⁻¹ * t i ∈ H := by simpa using H.one_mem
      have hval : indRep H χ t ht hc (t i) (Pi.single i0 1) = dot H χ (t i0) • Pi.single i (1 : ℂ) := by
        ext k
        show Matrix.toLin' (indMat H χ t (t i)) (Pi.single i0 1) k = _
        rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
        simp only [Matrix.col_apply, indMat, Pi.smul_apply, smul_eq_mul]
        by_cases hk : k = i
        · subst hk
          rw [Pi.single_eq_same, mul_one, inv_mul_cancel, one_mul]
        · rw [Pi.single_eq_of_ne hk, mul_zero]
          unfold dot
          rw [dite_eq_right]
          rw [memiff k i _ hti]
          exact hk
      have hne : dot H χ (t i0) ≠ 0 := by
        unfold dot
        rw [dite_eq_left hti0]
        exact Units.ne_zero _
      have : Pi.single i (1 : ℂ) = (dot H χ (t i0))⁻¹ • indRep H χ t ht hc (t i) (Pi.single i0 1) := by
        rw [hval, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t i, rfl⟩)
    intro x _
    rw [pi_eq_sum_univ x]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have e : (fun j => if i = j then (1 : ℂ) else 0) = Pi.single i 1 := by
      ext j; simp [Pi.single_apply, eq_comm]
    rw [e]; exact hsingle i
  · intro g
    rw [indRep_trace, ← indFun_eq_sum H χ t ht hc g]
    rfl

end GlobalTheory.InertiaEigenvalues

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingDiagOneUnitaryGroupEmbedding
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step

theorem isClosedEmbedding_embHom (r : ℕ) (E : Type) [CommRing E] [TopologicalSpace E] [T2Space E] :
    Topology.IsClosedEmbedding (embHom r E) := by
  have hc : Continuous (embHom r E) := by
    change Continuous fun g : Matrix (Fin r) (Fin r) E =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 (1 : Matrix (Fin 1) (Fin 1) E))
    exact (continuous_id.matrix_fromBlocks continuous_const continuous_const continuous_const).matrix_reindex _ _
  have hl : Function.LeftInverse
      (fun M : Matrix (Fin (r + 1)) (Fin (r + 1)) E => M.submatrix (Fin.castAdd 1) (Fin.castAdd 1))
      (embHom r E) := by
    intro g
    ext i j
    change (Matrix.fromBlocks g 0 0 (1 : Matrix (Fin 1) (Fin 1) E))
      (finSumFinEquiv.symm (Fin.castAdd 1 i)) (finSumFinEquiv.symm (Fin.castAdd 1 j)) = g i j
    rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
    rfl
  exact hl.isClosedEmbedding (continuous_id.matrix_submatrix _ _) hc

theorem isClosed_unitaryGroup (r : ℕ) (E : Type) [NormedField E] [StarRing E] [ContinuousStar E] :
    IsClosed (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) := by
  have : (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) = {M | M * Mᴴ = 1} := by
    ext M
    exact Matrix.mem_unitaryGroup_iff
  rw [this]
  exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const

theorem isClosedEmbedding_uEmb (r : ℕ) (E : Type) [NormedField E] [StarRing E] [ContinuousStar E] :
    Topology.IsClosedEmbedding (GlobalTheory.JR.Step.uEmb r E) := by
  have h1 : Topology.IsClosedEmbedding
      (Subtype.val : Matrix.unitaryGroup (Fin (r + 1)) E → Matrix (Fin (r + 1)) (Fin (r + 1)) E) :=
    (isClosed_unitaryGroup (r + 1) E).isClosedEmbedding_subtypeVal
  have h0 : Topology.IsClosedEmbedding
      (Subtype.val : Matrix.unitaryGroup (Fin r) E → Matrix (Fin r) (Fin r) E) :=
    (isClosed_unitaryGroup r E).isClosedEmbedding_subtypeVal
  rw [← h1.of_comp_iff]
  exact (isClosedEmbedding_embHom r E).comp h0

end GlobalTheory.JR.Step
end

