module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0384
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0602
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0612
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0613
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0605
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.OrthogonalInvarianceOfStableRankOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0534
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import GroundTheory.GlobalFields.TateThesis.Bundle0007
public import GroundTheory.GlobalFields.IdeleGroups.ClassGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAuxiliaryOfIsAuxiliaryCharacter
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.GridCharacters

theorem levelLe_of_le {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {m n : ℕ}
    (h : χ.LevelLe w m) (hmn : m ≤ n) : χ.LevelLe w n := fun x hx hx' =>
  h x hx (hx'.trans (WithZero.exp_le_exp.2 (by omega)))

theorem expAt_succ {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    (h : χ.LevelLe w (n + 1)) (h' : ¬ χ.LevelLe w n) : ExpAt χ w (n + 1) := fun m =>
  ⟨fun hm => by
    by_contra hlt
    exact h' (levelLe_of_le hm (by omega)), fun hm => levelLe_of_le h hm⟩

end GlobalTheory.LamTie.GridCharacters
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsSemistable
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory

theorem sst_isDR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → IsDR (P.PD K) ρ := by
  intro l _ P AI T K V _ _ _ ρ hρ
  obtain ⟨ι, -, hι⟩ := _root_.GlobalTheory.BstLog.iota_exists l P AI T
  let b := Module.finBasis ℚ_[l] V
  obtain ⟨Q, hQ⟩ := _root_.GlobalTheory.PMon.exists_periodMatrix_of_isSst l P AI T _ K V b ρ hρ
  refine _root_.GlobalTheory.PMon.isDR_of_periodMatrix l P _ K V b ρ (Matrix.GeneralLinearGroup.map ι.toRingHom Q) ?_
  intro g
  have hmap : ((Matrix.GeneralLinearGroup.map ι.toRingHom Q : GL (Fin (finrank ℚ_[l] V)) P.R.BdR) :
      Matrix (Fin (finrank ℚ_[l] V)) (Fin (finrank ℚ_[l] V)) P.R.BdR)
      = (Q : Matrix (Fin (finrank ℚ_[l] V)) (Fin (finrank ℚ_[l] V)) (Bst P)).map ι := rfl
  have h := congrArg (fun M => M.map ι) (hQ g)
  simp only [Matrix.map_mul, Matrix.map_map] at h
  rw [hmap]
  conv_rhs => rw [← h]
  congr 1
  · ext i j
    exact (ι.commutes _).symm
  · rw [Matrix.map_map]
    congr 1
    funext x
    exact (hι _ x).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDoubleCosetOfSmallerLevelSameLocalStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDoubleCoset_of_smaller_level_same_local : ∀ {G : Type} [Group G] (J J' Lc : Subgroup G) (x : G) (A : Finset G), J' ≤ J → J ⊓ Lc ≤ J' → (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ y ∈ Lc, Commute k₂ y) → x ∈ Lc → (∀ a ∈ A, a ∈ Lc) → Bridge.IsDC J x A → Bridge.IsDC J' x A := by
  first | exact @GlobalTheory.isDC_of_smaller_level_same_local | exact GlobalTheory.isDC_of_smaller_level_same_local | (intros; apply GlobalTheory.isDC_of_smaller_level_same_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKHwMap
section
noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links

namespace GlobalTheory.LowestKType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {n m : ℕ}

def kop (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m) : Module.End ℂ (PolF D m n) :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single a b (1 : ℂ))

def sop (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin n) : Module.End ℂ (PolF D m n) :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single a b (1 : ℂ))

def Cpt (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m) : Prop :=
  ((a : ℕ) < w.p τ ↔ (b : ℕ) < w.p τ)

def IsHarm (w : GlobalTheory.ExportSeries.Weight D n) (P : PolF D m n) : Prop :=
  ∀ (τ : D.what₂.Tau) (i l : Fin m), w.p τ ≤ (i : ℕ) → (l : ℕ) < w.p τ → kop w τ i l P = 0

def IsKHw (w : GlobalTheory.ExportSeries.Weight D n) (P : PolF D m n) : Prop :=
  (∀ (τ : D.what₂.Tau) (a b : Fin m), Cpt w τ a b → a < b → kop w τ a b P = 0) ∧
    ∀ (τ : D.what₂.Tau) (a : Fin m), ∃ c : ℂ, kop w τ a a P = c • P

def IsKHwMap {W : Type} [AddCommGroup W] [Module ℂ W] (w : GlobalTheory.ExportSeries.Weight D n)
    (ψ : W →ₗ[ℂ] PolF D m n) : Prop :=
  (∀ (τ : D.what₂.Tau) (a b : Fin m), Cpt w τ a b → a < b → kop w τ a b ∘ₗ ψ = 0) ∧
    ∀ (τ : D.what₂.Tau) (a : Fin m), ∃ c : ℂ, kop w τ a a ∘ₗ ψ = c • ψ

def IsNHw (w : GlobalTheory.ExportSeries.Weight D n) (lam : D.what₂.Tau → Fin n → ℂ) (P : PolF D m n) : Prop :=
  (∀ (τ : D.what₂.Tau) (a b : Fin n), a < b → sop w τ a b P = 0) ∧
    ∀ (τ : D.what₂.Tau) (a : Fin n), sop w τ a a P = lam τ a • P

end GlobalTheory.LowestKType

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableOfInvertiblePeriodMatrixSemistableRi
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

open Matrix

theorem isSst_of_periodMatrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V]
    (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) (Q : GL n (Bst P)),
    (∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] (Bst P)) *
      (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) → IsSst P ρ := by
  intro l _ P AI T n _ _ K V _ _ b ρ Q hQ
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    haveI := K.2
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  obtain ⟨crd, hcrd⟩ : ∃ crd : V ⊗[ℚ_[l]] Bst P ≃ₗ[ℚ_[l]] (n → Bst P),
      ∀ v c, crd (v ⊗ₜ c) = fun i => b.repr v i • c := by
    refine ⟨(TensorProduct.congr b.equivFun (LinearEquiv.refl _ _)) ≪≫ₗ TensorProduct.comm _ _ _ ≪≫ₗ
      TensorProduct.piScalarRight ℚ_[l] ℚ_[l] (Bst P) n, fun v c => ?_⟩
    funext i
    simp
  obtain ⟨ι, hι⟩ : ∃ ι : ↥(K0 K) →ₗ[ℚ_[l]] Bst P, ∀ c, ι c = Polynomial.C (algebraMap ↥(K0 K) P.R.B c) :=
    ⟨(Polynomial.CAlgHom.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B)).toLinearMap, fun _ => rfl⟩
  set M : ↥(GK K) → Matrix n n (Bst P) := fun g => (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] (Bst P))
    with hM

  have hact : ∀ g x, crd (stRep P ρ g x) = M g *ᵥ (fun i => actSt P (g : GQ l) (crd x i)) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero =>
      funext i
      simp only [map_zero, Pi.zero_apply]
      rw [show (fun _ : n => (0 : Bst P)) = 0 from rfl, Matrix.mulVec_zero, Pi.zero_apply]
    | tmul v c =>
      funext i
      rw [stRep_tmul, hcrd, hcrd, ← LinearMap.toMatrix_mulVec_repr b b (ρ g) v]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hM, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def, map_mul, AlgHom.commutes,
        map_sum, Finset.sum_mul, mul_assoc]
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy, ← Matrix.mulVec_add]
      congr 1
      funext i
      simp [map_add (f := _)]

  have hmv : ∀ (g : ↥(GK K)) (w : n → Bst P),
      (fun i => actSt P (g : GQ l) (((Q : Matrix n n (Bst P)) *ᵥ w) i)) =
        (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) *ᵥ (fun i => actSt P (g : GQ l) (w i)) := by
    intro g w
    funext i
    exact RingHom.map_mulVec ((actSt P (g : GQ l)) : Bst P →+* Bst P) _ w i
  have hQinv : ∀ w : n → Bst P, ((Q⁻¹ : GL n (Bst P)) : Matrix n n (Bst P)) *ᵥ ((Q : Matrix n n (Bst P)) *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, Q.inv_mul, Matrix.one_mulVec]
  have hQinv' : ∀ w : n → Bst P, (Q : Matrix n n (Bst P)) *ᵥ (((Q⁻¹ : GL n (Bst P)) : Matrix n n (Bst P)) *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, Q.mul_inv, Matrix.one_mulVec]
  let f : (n → ↥(K0 K)) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P :=
    crd.symm.toLinearMap ∘ₗ (((Q : Matrix n n (Bst P)).mulVecLin).restrictScalars ℚ_[l]) ∘ₗ LinearMap.compLeft ι n
  have hf : ∀ c, crd (f c) = (Q : Matrix n n (Bst P)) *ᵥ (fun i => ι (c i)) := by
    intro c
    simp [f, LinearMap.compLeft]
    rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h1 : (fun i => ι (c i)) = 0 := by
      have := hf c
      rw [hc, map_zero] at this
      rw [← hQinv (fun i => ι (c i)), ← this, Matrix.mulVec_zero]
    funext i
    have h2 := congrFun h1 i
    rw [hι, Pi.zero_apply, Polynomial.C_eq_zero] at h2
    exact (algebraMap ↥(K0 K) P.R.B).injective (h2.trans (map_zero _).symm)
  have hrange : LinearMap.range f = Dst P ρ := by
    ext x
    rw [mem_Dst, LinearMap.mem_range]
    constructor
    · rintro ⟨c, rfl⟩ g
      apply crd.injective
      rw [hact, hf, hmv, Matrix.mulVec_mulVec, hQ g]
      congr 1
      funext i
      exact ((_root_.GlobalTheory.PMon.stInv_iff l P AI T K (ι (c i))).mpr ⟨c i, hι _⟩) g
    · intro hx
      set z := ((Q⁻¹ : GL n (Bst P)) : Matrix n n (Bst P)) *ᵥ crd x with hz
      have hy : crd x = (Q : Matrix n n (Bst P)) *ᵥ z := (hQinv' _).symm
      have hinv : ∀ i g, actSt P ((g : ↥(GK K)) : GQ l) (z i) = z i := by
        intro i g
        have h1 := congrArg crd (hx g)
        rw [hact, hy, hmv, Matrix.mulVec_mulVec, hQ g] at h1
        have h2 := congrArg (fun w => ((Q⁻¹ : GL n (Bst P)) : Matrix n n (Bst P)) *ᵥ w) h1
        simp only [hQinv] at h2
        exact congrFun h2 i
      choose c hc using fun i => (_root_.GlobalTheory.PMon.stInv_iff l P AI T K (z i)).mp (hinv i)
      refine ⟨c, crd.injective ?_⟩
      rw [hf, hy]
      congr 1
      funext i
      rw [hι, hc i]
  unfold IsSst
  rw [← hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, Module.finrank_eq_card_basis b, mul_comm]

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSeriesUnfoldMirabolic
section
noncomputable section

open MeasureTheory GlobalTheory.CuspRep
open scoped ENNReal Matrix

namespace GlobalTheory.ThetaUnfold

variable {E : Type} [Field E] [NumberField E] {a : ℕ}



open NumberField Matrix GlobalTheory.MirTower in
theorem mem_mirU_pred {K : Type} [Field K] {a : ℕ} (ha : 0 < a) (γ : GL (Fin a) K) :
    γ ∈ mirU K a (a - 1) ↔ ∀ j, γ.val ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩ j =
      if j = ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩ then 1 else 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  exact mem_mirU_last


open NumberField Matrix GlobalTheory.MirTower in
theorem lintegral_theta_unfold : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕P : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (ratMirU E a (a - 1)) 𝓕P μ → ∀ F : GA E a → (Fin a → Ad E) → ℝ≥0∞, (∀ v : Fin a → E, Measurable fun g : GA E a => F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (v i)) g.val)) → (∀ (γ : GL (Fin a) E) g y, F (ratGL E a γ * g) y = F g y) → ∫⁻ g in 𝓕, ∑' ξ : {v : Fin a → E // v ≠ 0}, F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (ξ.1 i)) g.val) ∂μ = ∫⁻ g in 𝓕P, F g (g.val ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩) ∂μ := by
  intro E _ _ a ha μ _ 𝓕 𝓕P h𝓕 h𝓕P F hm hF
  set l : Fin a := ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩
  have hv : (Pi.single l 1 : Fin a → E) ≠ 0 := fun h0 => by simpa using congrFun h0 l
  have hP' : ∀ γ : GL (Fin a) E, γ ∈ mirU E a (a - 1) ↔ (Pi.single l 1 : Fin a → E) ᵥ* γ.val = Pi.single l 1 :=
    fun γ => by
      rw [mem_mirU_pred ha, Matrix.single_one_vecMul, funext_iff]
      simp only [Pi.single_apply, Matrix.row]
      rfl
  have he : algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin a → E) = (Pi.single l 1 : Fin a → Ad E) := by
    funext j
    simp only [Function.comp_apply, Pi.single_apply]
    split_ifs <;> simp
  have := lintegral_tsum_vecMul μ hv hP' h𝓕 h𝓕P F hF (hm _).aemeasurable
  simp only [he, Matrix.single_one_vecMul] at this
  exact this

end GlobalTheory.ThetaUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergFactorConjTendstoOneNeZeroStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localRankinSelbergFactor_conj_tendsto_one_ne_zero : ∀ (q : ℕ) (A B : Multiset ℂˣ), 1 < q → (∀ α ∈ A, ‖(α : ℂ)‖ ^ 2 < (q : ℝ)) → (∀ β ∈ B, ‖(β : ℂ)‖ ^ 2 < (q : ℝ)) → Tendsto (fun x : ℝ => locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (𝓝[>] 1) (𝓝 (locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) 1)) ∧ locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) 1 ≠ 0 := by
  first | (exact @GlobalTheory.JSW.locL_conj_tendsto_one_and_ne_zero) | (exact GlobalTheory.JSW.locL_conj_tendsto_one_and_ne_zero) | (intros; apply GlobalTheory.JSW.locL_conj_tendsto_one_and_ne_zero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMtMulLeftAdelicMatrixHaarEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

def matrixColumns (R : Type) [AddCommGroup R] (n m : ℕ) :
    Matrix (Fin n) (Fin m) R ≃+ (Fin m → Fin n → R) where
  toFun x j i := x i j
  invFun y := Matrix.of fun i j => y j i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem map_mul_left_eq_of_mulVec (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
    (n m : ℕ) (A : Matrix (Fin n) (Fin n) R)
    (hA : ∀ ν : Measure (Fin n → R), ν.IsAddHaarMeasure → ν.map A.mulVecLin = ν)
    (μ : @Measure (Matrix (Fin n) (Fin m) R) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (Matrix (Fin n) (Fin m) R) _ _ (borel _) μ) :
    @Measure.map _ _ (borel _) (borel _) (fun x : Matrix (Fin n) (Fin m) R => A * x) μ = μ := by
  letI mM : MeasurableSpace (Matrix (Fin n) (Fin m) R) := borel _
  haveI bM : BorelSpace (Matrix (Fin n) (Fin m) R) := ⟨rfl⟩
  letI mP : MeasurableSpace (Fin m → Fin n → R) := borel _
  haveI bP : BorelSpace (Fin m → Fin n → R) := ⟨rfl⟩
  let e := matrixColumns R n m
  have he : Continuous e := continuous_pi fun j => continuous_pi fun i =>
    (continuous_apply j).comp (continuous_apply i)
  have hes : Continuous e.symm := continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply i).comp (continuous_apply j)
  let φ : (Fin n → R) →+ (Fin n → R) := A.mulVecLin.toAddMonoidHom
  have hφ : Continuous φ := Continuous.matrix_mulVec continuous_const continuous_id
  haveI hν : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  have key := map_pi_eq_of_map_addHaar_eq (Fin n → R) φ hφ hA m (μ.map e) hν
  have hΦ : Continuous (fun (x : Fin m → Fin n → R) i => φ (x i)) :=
    continuous_pi fun i => hφ.comp (continuous_apply i)
  have hfac : (fun x : Matrix (Fin n) (Fin m) R => A * x) =
      e.symm ∘ (fun (x : Fin m → Fin n → R) i => φ (x i)) ∘ e := by
    funext x
    ext i j
    exact Matrix.mul_apply
  rw [hfac]
  calc μ.map (e.symm ∘ (fun (x : Fin m → Fin n → R) i => φ (x i)) ∘ e)
      = ((μ.map e).map (fun (x : Fin m → Fin n → R) i => φ (x i))).map e.symm := by
        rw [Measure.map_map hΦ.measurable he.measurable, Measure.map_map hes.measurable (hΦ.comp he).measurable]
    _ = (μ.map e).map e.symm := by rw [key]
    _ = μ := by
        rw [Measure.map_map hes.measurable he.measurable]
        have : (e.symm ∘ e : Matrix (Fin n) (Fin m) R → _) = id := by
          funext x; simp
        rw [this, Measure.map_id]

theorem map_mt_mul_eq : ∀ (D : D7) (V : HSp D) (m : ℕ) (g : GA D V) (μ : Measure (Mx D V.rank m)), μ.IsAddHaarMeasure → μ.map (fun x : Mx D V.rank m => (HMul.hMul (mt V g) (x : Matrix (Fin V.rank) (Fin m) (AE D)) : Mx D V.rank m)) = μ := by
  intro D V m g μ hμ
  refine map_mul_left_eq_of_mulVec (AE D) V.rank m (mt V g) ?_ μ hμ
  intro ν hν
  exact PI.VolSemiDirect.W.Cj.unipotent_modulus_holds _ _ D.sp.cm.sig (GlobalTheory.Mem.VolExists.isCMExt D.sp.cm) V.rank V.gram (GlobalTheory.Mem.VolExists.isHermND D.sp.cm V) g ν hν

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMulRightUnitaryGramAdelicMatrixHaarEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem mul_unitary_map_haar : ∀ (D : D7) (N m : ℕ) (K : Matrix (Fin N) (Fin N) D.host.E), (∀ a b, D.sp.cm.sig (K b a) = K a b) → K.det ≠ 0 → ∀ (g : HA (AF D.host.F) D.sp.cm.sig K) (μ : Measure (Mx D m N)), μ.IsAddHaarMeasure → μ.map (fun x : Mx D m N => (HMul.hMul (x : Matrix (Fin m) (Fin N) (AE D)) ((HA.mat (AF D.host.F) D.sp.cm.sig K g).1 : Matrix (Fin N) (Fin N) (AE D)) : Mx D m N)) = μ := by
  intro D N m K hK hdet g μ hμ
  have hcm := GlobalTheory.Mem.VolExists.isCMExt D.sp.cm
  let A : Matrix (Fin N) (Fin N) (AE D) := (HA.mat (AF D.host.F) D.sp.cm.sig K g).1
  let φ : (Fin N → AE D) →+ (Fin N → AE D) :=
    { toFun := fun v => Matrix.vecMul v A
      map_zero' := Matrix.zero_vecMul A
      map_add' := fun a b => Matrix.add_vecMul A a b }
  have hφ : Continuous φ := continuous_id.matrix_vecMul continuous_const
  exact GlobalTheory.map_pi_eq_of_map_addHaar_eq (Fin N → AE D) φ hφ
    (fun ν hν => GlobalTheory.AdelicModulus.Row.map_vecMul_unitary _ _ D.sp.cm.sig hcm N K ⟨fun i j => hK i j, hdet⟩ g ν hν) m μ hμ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNatMultipleIntegralFiniteAdelesIffIdealFinite
section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.RSJ

open IsDedekindDomain.HeightOneSpectrum WithZero

theorem valued_natCast_apply (E : Type) [Field E] [NumberField E] (N : ℕ)
    (v : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((N : FiniteAdeleRing (𝓞 E) E) v) = v.valuation E (N : E) := by
  rw [← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)) N]
  exact valuedAdicCompletion_eq_valuation' v (N : E)

theorem natLat_iff_mem_idealFiniteAdeles : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
      (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) →
      ∀ z : FiniteAdeleRing (𝓞 E) E, z ∈ GlobalTheory.RSJ.natLat E N ↔ z ∈ GroundTheory.Global.idealFiniteAdeles J := by
  intro E _ _ N hN J hJ x
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hc0 : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (N : E) ≠ 0 :=
    fun v => (Valuation.ne_zero_iff _).2 hN0
  have hc : ∀ v : HeightOneSpectrum (𝓞 E),
      exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) = v.valuation E (N : E) := by
    intro v
    rw [hJ, GroundTheory.Global.count_spanSingleton v hN0, neg_neg, exp_log (hc0 v)]
  rw [GroundTheory.Global.mem_idealFiniteAdeles]
  simp only [hc]
  have hunit : (N : FiniteAdeleRing (𝓞 E) E) * algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)) N, ← map_mul, mul_inv_cancel₀ hN0,
      map_one]
  constructor
  · rintro ⟨z, hz, rfl⟩ v
    change Valued.v ((N : FiniteAdeleRing (𝓞 E) E) v * z v) ≤ _
    rw [map_mul, valued_natCast_apply]
    have : Valued.v (z v) ≤ 1 := by
      have h := hz v
      rwa [mem_adicCompletionIntegers] at h
    calc v.valuation E (N : E) * Valued.v (z v) ≤ v.valuation E (N : E) * 1 := by gcongr
      _ = _ := mul_one _
  · intro hx
    refine ⟨algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹ * x, fun v => ?_, ?_⟩
    · rw [mem_adicCompletionIntegers]
      change Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹) v * x v) ≤ 1
      rw [map_mul]
      change Valued.v (((N : E)⁻¹ : E) : v.adicCompletion E) * Valued.v (x v) ≤ 1
      rw [valuedAdicCompletion_eq_valuation' v, map_inv₀]
      exact (GroundTheory.Global.inv_mul_le_one_iff_withZero (hc0 v)).2 (hx v)
    · rw [← mul_assoc, hunit, one_mul]

end GlobalTheory.RSJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormProdSatakeParametersUnitaryEqOneStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_prod_satakeParameters_unitary_eq_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ : CG E a) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), σ.IsUnitary → σ.HasSat w B → ‖((B.prod : ℂˣ) : ℂ)‖ = 1 := by
  first | (exact @GlobalTheory.RSNonvan.norm_prod_sat_eq_one) | (exact GlobalTheory.RSNonvan.norm_prod_sat_eq_one) | (intros; apply GlobalTheory.RSNonvan.norm_prod_sat_eq_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSublevelFiniteIndexMorePlacesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricSublevel_finiteIndex_more_places : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → (levEnv V β { L with Q := Q', xq := xq }).J ≤ (levEnv V β L).J ∧ (levEnv V β { L with Q := Q', xq := xq }).Q ≤ (levEnv V β L).Q ∧ (((levEnv V β { L with Q := Q', xq := xq }).J).subgroupOf (levEnv V β L).J).FiniteIndex ∧ ∀ g : Bridge.Gf V, g ∈ (levEnv V β { L with Q := Q', xq := xq }).Q → g ∈ (levEnv V β L).J → g ∈ (levEnv V β { L with Q := Q', xq := xq }).J := by
  first | exact @GlobalTheory.sublevel_finiteIndex | exact GlobalTheory.sublevel_finiteIndex | (intros; apply GlobalTheory.sublevel_finiteIndex <;> assumption)
end

