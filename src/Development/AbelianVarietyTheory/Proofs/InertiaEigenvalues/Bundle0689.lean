module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0642
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCoefficientSpaceDualDiscreteSeriesModelPos
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0274
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0675
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0677
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralLowestKTypeMatrixCoeffSqPos
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.LowCoefPos

theorem integral_lowCoefSq_pos : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, LevProd R i → ∀ v, IsUnitVec R i v → IntegrableOn (lowCoefSq R i v) (realLev R i) (R.νW i) → 0 < ∫ h in realLev R i, lowCoefSq R i v h ∂(R.νW i) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i hP v hv hI
  have hθ : IsInfFam R.θ := hL.models.inf
  have : (R.νW i).IsHaarMeasure := (hL.models.νW i).1.1

  have hrep : ∀ ρ (x : (R.MW i (sg0 D A)).H ρ), Continuous fun h : GA D (Wc D i) =>
      (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) h) x := by
    intro ρ x
    have hmem : ∀ h : GA D (Wc D i), (R.MW i (sg0 D A)).fr ρ * infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) h * ((R.MW i (sg0 D A)).fr ρ)⁻¹ ∈ UJset ((R.MW i (sg0 D A)).ε ρ) :=
      fun h => GlobalTheory.DualCoef.frame_mem (R.MW i (sg0 D A)) ρ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ (Wc D i) h ρ)
    exact (((R.MW i (sg0 D A)).ds ρ).2.2.1.2.2 x).comp_continuous
      ((continuous_const.matrix_mul (GlobalTheory.Mem.VolExists.continuous_infMat (Wc D i).gram (hθ ρ))).matrix_mul
        continuous_const) hmem
  have hc : Continuous (lowCoefSq R i v) := by
    unfold lowCoefSq
    refine (continuous_finsetProd _ fun ρ _ => ?_).norm.pow 2
    exact continuous_const.inner (hrep ρ _)

  have h0 : ∀ h, 0 ≤ lowCoefSq R i v h := fun h => by unfold lowCoefSq; positivity

  have h1 : lowCoefSq R i v 1 = 1 := by
    unfold lowCoefSq
    have e : ∀ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ), (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) 1)
        ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ = 1 := by
      intro ρ
      rw [GlobalTheory.PointAtPlaceHom.infMat_one, GlobalTheory.DualCoef.rep_one, ContinuousLinearMap.one_apply,
        inner_self_eq_norm_sq_to_K, hv ρ]
      simp
    simp [e]

  set O : Set (GA D (Wc D i)) := GlobalTheory.AutMult.toFin (Wc D i) ⁻¹'
    {g : GfC (Wc D i) | (g : GA D (Wc D i)) ∈ levG _ (R.βW i) (R.datWp i R.triv)} with hO
  have hOo : IsOpen O := (GlobalTheory.LevelOpen.isOpen_levG _ _ _).preimage (GlobalTheory.AutMult.continuous_toFin _)
  have hOs : O ⊆ realLev R i := by
    intro h hh
    exact ⟨_, (GlobalTheory.AutMult.toInf (Wc D i) h).2, _, hh, (GlobalTheory.AutMult.toInf_mul_toFin h).symm⟩
  have h1O : (1 : GA D (Wc D i)) ∈ O := by
    show ((GlobalTheory.AutMult.toFin (Wc D i) 1 : GfC (Wc D i)) : GA D (Wc D i)) ∈ levG _ (R.βW i) (R.datWp i R.triv)
    rw [map_one]
    exact (levW R i).one_mem
  set U : Set (GA D (Wc D i)) := {h | (1 : ℝ) / 2 < lowCoefSq R i v h} ∩ O with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const hc).inter hOo
  have h1U : (1 : GA D (Wc D i)) ∈ U := ⟨by rw [Set.mem_setOf_eq, h1]; norm_num, h1O⟩
  have hUs : U ⊆ Function.support (lowCoefSq R i v) ∩ realLev R i := by
    intro h hh
    refine ⟨?_, hOs hh.2⟩
    have := hh.1
    rw [Set.mem_setOf_eq] at this
    rw [Function.mem_support]
    linarith
  have hpos : 0 < R.νW i U := hUo.measure_pos _ ⟨1, h1U⟩
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall h0) hI]
  exact lt_of_lt_of_le hpos (measure_mono hUs)

end GlobalTheory.LowCoefPos

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableLatticeInMatrixAlgebraLayer
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.LayerSst

open Module

section Sum

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ_[l] (V i)]
  {V' : Type} [AddCommGroup V'] [Module ℚ_[l] V']
  {ρ : ∀ i, Representation ℚ_[l] ↥(GK K) (V i)} {ρ' : Representation ℚ_[l] ↥(GK K) V'}
  {E : V' ≃ₗ[ℚ_[l]] (∀ i, V i)}
  (hE : ∀ g x i, E (ρ' g x) i = ρ i g (E x i))
include hE

theorem mem_Dst_iff (x : V' ⊗[ℚ_[l]] Bst P) :
    x ∈ Dst P ρ' ↔ ∀ i, GlobalTheory.BlockSum.tensComp E (Bst P) x i ∈ Dst P (ρ i) := by
  simp only [mem_Dst]
  rw [forall_comm]
  refine forall_congr' fun g => ?_
  rw [← (GlobalTheory.BlockSum.tensComp E (Bst P)).injective.eq_iff, funext_iff]
  refine forall_congr' fun i => ?_
  have key : GlobalTheory.BlockSum.tensComp E (Bst P) (stRep P ρ' g x) i =
      stRep P (ρ i) g (GlobalTheory.BlockSum.tensComp E (Bst P) x i) :=
    GlobalTheory.BlockSum.tensComp_map E (ρ' g) (fun i => ρ i g) (hE g) (actSt P (g : GQ l)).toLinearMap x i
  rw [key]

theorem isSst_sum [∀ i, FiniteDimensional ℚ_[l] (V i)] (h : ∀ i, IsSst P (ρ i)) : IsSst P ρ' := by
  have := fun i => finiteDimensional_Dst_of_isSst l P K (V i) (ρ i) (h i)
  unfold IsSst at h ⊢
  rw [GlobalTheory.BlockSum.finrank_eq_sum (GlobalTheory.BlockSum.tensComp E (Bst P)) _ _ (mem_Dst_iff P hE), E.finrank_eq,
    Module.finrank_pi_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => h i

end Sum

theorem isSst_resQ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (ρ : Representation LL ↥(GK K) V) (h : IsSst P ρ) : IsSst P (GlobalTheory.PstCoeff.resQ ρ) := by
  have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
    ext x
    simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
  have e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) = finrank ℚ_[l] LL * finrank LL ↥(Dst P ρ) := by
    rw [hD, finrank_mul_finrank]
    rfl
  rw [IsSst, e, h, ← finrank_mul_finrank ℚ_[l] LL V]
  ring

section Layer

variable {l : ℕ} [Fact l.Prime] {K L₀ : FinExt l} {a d : ℕ} {Cl : Set (↥(GK K) →* GL (Fin a) (Om l))}
  {ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]} (Ly : Layer L₀ Cl ρ)

def matL (k : Fin Ly.m) (g : ↥(GK K)) : Matrix (Fin a) (Fin a) ↥(Ly.L k).1 :=
  fun i j => ⟨(Ly.rep k g).val i j, Ly.rep_mem k g i j⟩

def repL (k : Fin Ly.m) : ↥(GK K) →* GL (Fin a) ↥(Ly.L k).1 :=
  MonoidHom.toHomUnits
    { toFun := matL Ly k
      map_one' := by
        ext i j
        simp only [matL, map_one, Units.val_one, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := fun g h => by
        ext i j
        simp [matL, Matrix.mul_apply] }

theorem repL_val (k : Fin Ly.m) (g : ↥(GK K)) (i j : Fin a) :
    (((repL Ly k g).val i j : ↥(Ly.L k).1) : Om l) = (Ly.rep k g).val i j := rfl

def RL (k : Fin Ly.m) : Representation ↥(Ly.L k).1 ↥(GK K) (Fin a → ↥(Ly.L k).1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥(Ly.L k).1 ≃ₐ[↥(Ly.L k).1] _) : _ →* _).comp
    ((Units.coeHom _).comp (repL Ly k))

theorem RL_apply (k : Fin Ly.m) (g : ↥(GK K)) (v : Fin a → ↥(Ly.L k).1) : RL Ly k g v = (repL Ly k g).val *ᵥ v := by
  simp [RL, Matrix.toLinAlgEquiv'_apply]

def coordM (v : Fin d → ℚ_[l]) (k : Fin Ly.m) : Matrix (Fin a) (Fin a) (Om l) :=
  ∑ s, algebraMap ℚ_[l] (Om l) (v s) • Ly.b s k

theorem coordM_mem (v : Fin d → ℚ_[l]) (k : Fin Ly.m) (i j : Fin a) : coordM Ly v k i j ∈ (Ly.L k).1 := by
  simp only [coordM, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact sum_mem fun s _ => mul_mem (IntermediateField.algebraMap_mem _ _) (Ly.b_mem s k i j)

theorem sum_b (v : Fin d → ℚ_[l]) : ∑ s, v s • Ly.b s = fun k => coordM Ly v k := by
  funext k
  simp [coordM, Finset.sum_apply, algebraMap_smul]

end Layer

section Layer2

variable {l : ℕ} [Fact l.Prime] {K L₀ : FinExt l} {a d : ℕ} {Cl : Set (↥(GK K) →* GL (Fin a) (Om l))}
  {ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]} (Ly : Layer L₀ Cl ρ)

def coordLin : (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] ((p : Fin Ly.m × Fin a) → Fin a → ↥(Ly.L p.1).1) where
  toFun v p i := ⟨coordM Ly v p.1 i p.2, coordM_mem Ly v p.1 i p.2⟩
  map_add' v w := by
    funext p i
    apply Subtype.ext
    simp [coordM, Finset.sum_add_distrib, add_smul, Matrix.sum_apply]
  map_smul' c v := by
    funext p i
    apply Subtype.ext
    show coordM Ly (c • v) p.1 i p.2 = c • coordM Ly v p.1 i p.2
    simp only [coordM, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, map_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Algebra.smul_def, mul_assoc]

theorem coordLin_apply (v : Fin d → ℚ_[l]) (p : Fin Ly.m × Fin a) (i : Fin a) :
    ((coordLin Ly v p i : ↥(Ly.L p.1).1) : Om l) = coordM Ly v p.1 i p.2 := rfl

theorem coordLin_bijective : Function.Bijective (coordLin Ly) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h0 : ∑ s, v s • Ly.b s = 0 := by
      rw [sum_b]
      funext k i j
      have := congrArg Subtype.val (congrFun (congrFun hv (k, j)) i)
      exact this
    exact funext (Fintype.linearIndependent_iff.1 Ly.indep v h0)
  · intro y
    let x : Fin Ly.m → Matrix (Fin a) (Fin a) (Om l) := fun k i j => ((y (k, j) i : ↥(Ly.L k).1) : Om l)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ_[l]).1 (Ly.span x fun k i j => (y (k, j) i).2)
    refine ⟨c, ?_⟩
    funext p i
    apply Subtype.ext
    rw [coordLin_apply]
    rw [sum_b] at hc
    exact congrFun (congrFun (congrFun hc p.1) i) p.2

def coordEquiv : (Fin d → ℚ_[l]) ≃ₗ[ℚ_[l]] ((p : Fin Ly.m × Fin a) → Fin a → ↥(Ly.L p.1).1) :=
  LinearEquiv.ofBijective (coordLin Ly) (coordLin_bijective Ly)

theorem coordM_mulVec (g : ↥(GK K)) (v : Fin d → ℚ_[l]) (k : Fin Ly.m) :
    coordM Ly (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v) k = (Ly.rep k g).val * coordM Ly v k := by
  have hr : ∀ t, (Ly.rep k g).val * Ly.b t k = ∑ s, zOm l ((ρ g).val s t) • Ly.b s k :=
    fun t => (Ly.reads k).equi g t
  calc coordM Ly (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v) k
      = ∑ s, ∑ t, (algebraMap ℚ_[l] (Om l) (v t) * zOm l ((ρ g).val s t)) • Ly.b s k := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [coordM, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_smul, Matrix.map_apply]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
        rw [mul_comm]
        rfl
    _ = ∑ t, ∑ s, (algebraMap ℚ_[l] (Om l) (v t) * zOm l ((ρ g).val s t)) • Ly.b s k := Finset.sum_comm
    _ = (Ly.rep k g).val * coordM Ly v k := by
        simp only [coordM, Finset.mul_sum, Matrix.mul_smul, hr, Finset.smul_sum, smul_smul]

theorem coordEquiv_equi (g : ↥(GK K)) (v : Fin d → ℚ_[l]) (p : Fin Ly.m × Fin a) :
    coordEquiv Ly (qRep ρ g v) p = GlobalTheory.PstCoeff.resQ (RL Ly p.1) g (coordEquiv Ly v p) := by
  funext i
  apply Subtype.ext
  have hq : qRep ρ g v = ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v := by
    simp [qRep, Matrix.toLinAlgEquiv'_apply]
  rw [GlobalTheory.PstCoeff.resQ_apply, RL_apply]
  change coordM Ly (qRep ρ g v) p.1 i p.2 = _
  rw [hq, coordM_mulVec, Matrix.mul_apply]
  simp [Matrix.mulVec, dotProduct, repL_val, coordEquiv, coordLin_apply]

end Layer2

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ) (Cl : Set (↥(GK K) →* GL (Fin a) (Om l))) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Ly : Layer L₀ Cl ρ), ((∀ ρ₁ ∈ Cl, ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R) → IsSst P (qRep ρ)) ∧ ((∀ ρ₁ ∈ Cl, (∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsCrys (P.PD K) R)) → IsCrys (P.PD K) (qRep ρ)) := by
  intro l _ K L₀ P AI T a Cl d ρ Ly
  have hfin : ∀ p : Fin Ly.m × Fin a, FiniteDimensional ℚ_[l] (Fin a → ↥(Ly.L p.1).1) := fun p => by
    have := (Ly.L p.1).2
    infer_instance
  have hE := coordEquiv_equi Ly
  refine ⟨fun hS => ?_, fun hC => ?_⟩
  · refine isSst_sum P (E := coordEquiv Ly) (fun g x p => hE g x p) fun p => ?_
    have := (Ly.L p.1).2
    exact isSst_resQ P _ (hS (Ly.rep p.1) (Ly.mem p.1) (Ly.L p.1) (repL Ly p.1) (RL Ly p.1) (Ly.le p.1)
      (fun g v => RL_apply Ly p.1 g v) (fun g i j => repL_val Ly p.1 g i j))
  · refine GlobalTheory.BlockSum.isCrys_sum (P.PD K) (E := coordEquiv Ly) (fun g x p => hE g x p) fun p => ?_
    have := (Ly.L p.1).2
    exact (GlobalTheory.BSCoeff.isCrys_resQ_iff P (RL Ly p.1)).2 (hC (Ly.rep p.1) (Ly.mem p.1) (Ly.L p.1) (repL Ly p.1)
      (RL Ly p.1) (Ly.le p.1) (fun g v => RL_apply Ly p.1 g v) (fun g i j => repL_val Ly p.1 g i j))

end GlobalTheory.LayerSst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionInjective
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.LExtInj

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_irreducible_GL_zero : ∃ t : IrrGL (k := k), t.1 = 0 ∧ IsL (0 : Multiset (Segment k)) t.rep :=
  ⟨IrrGL.of (detRep (Fin 0) (1 : kˣ →* ℂˣ)) ((isSmooth_ofChar_iff _).2 isSmoothChar_one.detChar)
    (isIrreducible_ofChar _), rfl, (Tests.empty_spec (k := k)).2.of_equiv (IrrGL.equivOf _ _ _)⟩

theorem sum_fst_of_lFactors' {𝔪 : Multiset (Segment k)} {c : ℕ} {x : Fin c → IrrGL (k := k)} (hx : LFactors 𝔪 x) :
    ∑ a, (x a).1 = (𝔪.map Segment.deg).sum := by
  obtain ⟨Δ, ⟨rfl, -⟩, hΔ⟩ := hx
  rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  exact Finset.sum_congr rfl fun a _ => (hΔ a).deg_eq.symm

theorem deg_of_isL' {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} {𝔪 : Multiset (Segment k)}
    {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π) : (𝔪.map Segment.deg).sum = N := by
  obtain ⟨_, x, hd, hx, -⟩ := h
  exact (sum_fst_of_lFactors' hx).symm.trans hd

theorem eq_of_isL (hM : LanglandsMultisegments) [CharZero k] (𝔪 : Multiset (Segment k)) (x y : IrrGL (k := k))
    (hx : IsL 𝔪 x.rep) (hy : IsL 𝔪 y.rep) : x = y := by
  obtain ⟨t, ht0, ht⟩ := exists_irreducible_GL_zero (k := k)
  have hdeg : x.1 = y.1 := (deg_of_isL' hx).symm.trans (deg_of_isL' hy)
  obtain ⟨nx, cx⟩ := x
  obtain ⟨ny, cy⟩ := y
  obtain rfl : nx = ny := hdeg
  have hd : ∑ a, (![(⟨nx, cx⟩ : IrrGL (k := k)), t] a).1 = nx := by simp [Fin.sum_univ_two, ht0]
  have hs := (hM k).2 𝔪 0 ![⟨nx, cx⟩, t] ⟨nx, cy⟩ hd hx ht (by rwa [add_zero])
  obtain ⟨φ⟩ := GlobalTheory.T.nonempty_equiv_prodChosenIrrGL_pair_degreeZero k (⟨nx, cx⟩ : IrrGL (k := k)) t ht0 hd
  have hs2 : IsSubquotient (IrrGL.rep (⟨nx, cy⟩ : IrrGL (k := k))) (IrrGL.rep (⟨nx, cx⟩ : IrrGL (k := k))) :=
    hs.trans (.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective)
  obtain ⟨ψ⟩ := hs2.nonempty_equiv cy.rep.irr cx.rep.irr
  congr 1
  rw [← cx.cl_rep, ← cy.cl_rep]
  exact IrrRep.cl_eq_iff.2 ⟨ψ⟩

end Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem isIrrWD_lpTw {y : WD h} (hy : IsIrrWD y) (s : ℝ) : IsIrrWD (y.lpTw s) := by
  obtain ⟨n, a, rfl, ha⟩ := hy
  exact ⟨n, a.tw s, (WD.lpTw_mk a s).symm, isIrreducible_twist ha _⟩

theorem lpTw_injective {y y' : WD h} {s : ℝ} (e : y.lpTw s = y'.lpTw s) : y = y' := by
  have := congrArg (fun z : WD h => z.lpTw (-s)) e
  simpa only [WD.lpTw_add, add_neg_cancel, WD.lpTw_zero] using this

end GlobalTheory.LocLanglands.LExtInj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateTwistTotalWeightZeroProof
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Twist

variable {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]

theorem fr_mul_of_fixed (r N : ℕ) (c : ↥(MaximalUnramifiedExtension l)) (h : fr l r c = c) : fr l (r * N) c = c := by
  induction N with
  | zero => simp [fr]
  | succ k ih =>
    change (frobUr l ^ (r * (k + 1))) c = c
    rw [Nat.mul_succ, pow_add, AlgHom.mul_apply]
    change (frobUr l ^ (r * k)) (fr l r c) = c
    rw [h]
    exact ih

theorem isRat_twist {K K' : FinExt l} (hK : K.1 ≤ K'.1) (r N : ℕ) (hN : 0 < N) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l))
    (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (a : ℤ) (hρ : IsRat r ρ)
    (hle : ∀ c : ↥(MaximalUnramifiedExtension l), fr l (r * N) c = c → (c : Om l) ∈ K'.1) (hfr : ∀ g, fr l (r * N) (χ g : ↥(MaximalUnramifiedExtension l)) = χ g)
    (hcont : Continuous fun g => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l)) :
    IsRat (r * N) (twist hK ρ χ a) := ⟨Nat.mul_pos hρ.pos hN, hle, fun g i j => by
    rw [twist_val, Matrix.smul_apply, smul_eq_mul, map_mul, fr_mul_of_fixed r N _ (hρ.rat _ i j),
      Units.val_zpow_eq_zpow_val, map_zpow₀, hfr], fun i j => by
    have h1 : Continuous fun g : ↥(GK K') => (((ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) :=
      (hρ.cont i j).comp (continuous_subtype_val.subtype_mk _)
    have h2 : Continuous fun g : ↥(GK K') => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l) ^ a :=
      hcont.zpow₀ _ fun g => Or.inl (by
        intro h0
        exact (χ g).ne_zero (Subtype.ext h0))
    refine (h2.mul h1).congr fun g => ?_
    simp only [twist_val, Matrix.smul_apply, smul_eq_mul, Units.val_zpow_eq_zpow_val]
    push_cast
    rfl⟩

theorem potentiallySemistable_of_lubinTateTwist (P : LocPrime l) {K K' : FinExt l} (hK : K.1 ≤ K'.1) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l))
    (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (x : P.R.Bˣ) (a : ℤ)
    (hact : ∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) :
    AdmSt P (twist hK ρ χ a) → AdmSt P ρ := by
  have msmul : ∀ {R S : Type} [CommRing R] [CommRing S] {F : Type} [FunLike F R S] [RingHomClass F R S] (f : F) (c : R)
      (M : Matrix n n R), (c • M).map f = f c • M.map f := fun f c M => by
    ext i j; simp
  rintro ⟨K'', hK'', Q', hQ'⟩
  refine ⟨K'', hK.trans hK'', scalGL n (Units.map (Polynomial.C : P.R.B →+* Bst P).toMonoidHom (x ^ a)) * Q', fun g => ?_⟩
  have hg := hQ' g
  rw [twist_val, msmul, Matrix.smul_mul] at hg
  set g' : ↥(GK K') := ⟨(g : GQ l), GK_le hK'' g.2⟩
  have hx : Units.map (P.actQ (g : GQ l) : P.R.B →* P.R.B) x =
      Units.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B : ↥(MaximalUnramifiedExtension l) →* P.R.B) (χ g') * x := by
    apply Units.ext
    simpa using hact g'
  have hxa : actSt P (g : GQ l) (Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B)) =
      ks P ((χ g' ^ a : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) * Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B) := by
    have h2 := congrArg (fun u : P.R.Bˣ => Polynomial.C ((u ^ a : P.R.Bˣ) : P.R.B)) hx
    have e1 : ((Units.map (P.actQ (g : GQ l) : P.R.B →* P.R.B) x ^ a : P.R.Bˣ) : P.R.B) =
        P.actQ (g : GQ l) ((x ^ a : P.R.Bˣ) : P.R.B) := by rw [← map_zpow]; rfl
    have e2 : ((Units.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B : ↥(MaximalUnramifiedExtension l) →* P.R.B) (χ g') ^ a : P.R.Bˣ) : P.R.B) =
        algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ((χ g' ^ a : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) := by rw [← map_zpow]; rfl
    simp only [mul_zpow] at h2
    rw [e1, Units.val_mul, e2, map_mul] at h2
    rw [actSt_C]
    exact h2
  rw [scalGL_mul_val, msmul, Matrix.mul_smul, Units.coe_map]
  change actSt P (g : GQ l) (Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B)) • _ =
    Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B) • _
  rw [hxa]
  conv_rhs => rw [← hg]
  rw [smul_smul, mul_comm (Polynomial.C _)]

omit [DecidableEq n] in
theorem sum_weights (r N : ℕ) (hr : 0 < r) (w : Fin r → n → ℤ) (hN : Fintype.card n = N) :
    ∑ m : Fin (r * N), ∑ j, (w ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩ j + if (m : ℕ) = 0 then -∑ m, ∑ j, w m j else 0) = 0 := by
  subst hN
  simp only [Finset.sum_add_distrib]
  have key : ∀ N : ℕ, ∑ i ∈ Finset.range (r * N), (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j) i =
      N * ∑ m, ∑ j, w m j := by
    intro N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      have : ∑ x ∈ Finset.range r, (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j) (r * k + x) =
          ∑ m, ∑ j, w m j := by
        rw [← Fin.sum_univ_eq_sum_range (fun x => (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j) (r * k + x))]
        refine Finset.sum_congr rfl fun m _ => ?_
        have e : (⟨(r * k + (m : ℕ)) % r, Nat.mod_lt _ hr⟩ : Fin r) = m := by
          apply Fin.ext
          simp only
          rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt m.2]
        simp only [e]
      rw [this]
      push_cast
      ring
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j), key]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i : ℕ => if i = 0 then -∑ m, ∑ j, w m j else 0),
    Finset.sum_ite_eq' (Finset.range _) 0]
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
  · simp [h0]
  · rw [if_pos (Finset.mem_range.mpr (Nat.mul_pos hr h0))]
    ring

end GlobalTheory.PMon.Twist

namespace GlobalTheory.PMon

theorem twistStep : TwistStep := by
  intro l _ P AI T n _ _ K r ρ w hρ hw
  by_cases hn : Fintype.card n = 0
  · refine ⟨K, r, ρ, w, hρ, hw, ?_, id⟩
    have : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    simp
  · have hN : 0 < Fintype.card n := Nat.pos_of_ne_zero hn
    have hs : 0 < r * Fintype.card n := Nat.mul_pos hρ.pos hN
    obtain ⟨K', hK, x, χ, hle, hfr, hcont, hact, h1, h2, hj⟩ := _root_.GlobalTheory.LTChar.main l P AI T K (r * Fintype.card n) hs
    exact ⟨K', r * Fintype.card n, Twist.twist hK ρ χ (-∑ m, ∑ j, w m j), _,
      Twist.isRat_twist hK r _ hN ρ χ _ hρ hle hfr hcont,
      _root_.GlobalTheory.PMon.Twist.framed_twist l P AI T n K K' hK r (Fintype.card n) hρ.pos ρ w χ x _ hρ hw hact h1 h2 hj,
      Twist.sum_weights r _ hρ.pos w rfl, Twist.potentiallySemistable_of_lubinTateTwist P hK ρ χ x _ hact⟩

end GlobalTheory.PMon

end
end

