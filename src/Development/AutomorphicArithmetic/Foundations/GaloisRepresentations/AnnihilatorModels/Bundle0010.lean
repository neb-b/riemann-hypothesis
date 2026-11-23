module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PStOfCr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem boundQ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) :
    Bound (σSt P K) ℚ_[l] (finrank ℚ_[l] ↥(K0 K)) := by
  intro U _ m₁ m₂ hts _ ρ
  have hm : m₂ = m₁ := by
    refine Module.ext' _ _ fun a u => ?_
    have h := hts.smul_assoc a (1 : ℚ_[l]) u
    rw [smul_eq_mul, mul_one, @one_smul ℚ_[l] U _ m₁.toDistribMulAction.toMulAction] at h
    exact h.symm
  subst hm
  obtain ⟨hfin, hb⟩ := GlobalTheory.CrysSst.finrank_Dst_le P AI T ρ
  rw [dinv_σSt]
  exact ⟨hfin, by rw [mul_comm]; exact hb⟩

private theorem pow_C {l : ℕ} [Fact l.Prime] (P : LocPrime l) (f : ℕ) (b : P.R.B) :
    (Polynomial.C ((ψCr P f) b) : Bst P) = (ψSt P f) (Polynomial.C b) := by
  induction f generalizing b with
  | zero => simp [ψCr, ψSt]
  | succ f ih =>
    simp only [ψCr, ψSt, pow_succ', Module.End.mul_apply] at ih ⊢
    rw [← ih]
    simp

theorem UpperTheory.Gal.crystallineComparison.stOfCr_of :
    AnnPer → BoundSt → StOfCr := by
  intro hP _ l _ P AI hT K V _ _ _ ρ hA
  obtain ⟨T⟩ := hT
  have hB := boundQ P AI T K
  have key : ∀ f : ℕ, _ := fun f => hP ℚ_[l] ↥(GK K) P.R.B (Bst P) (σCr P K) (ψCr P f) (σSt P K) (ψSt P f)
    (Polynomial.CAlgHom : P.R.B →ₐ[ℚ_[l]] Bst P).toLinearMap Polynomial.C_injective
    (fun g b => (actSt_C P (g : GQ l) b).symm) (fun b => pow_C P f b) ℚ_[l] _ hB V ρ hA
  exact ⟨(key 0).1, fun f q n T' h => (key f).2 q n T' h⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PUnrGeom
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.unrGeom_of :
    UnrOfGeom := by
  classical
  intro E Ω _ _ _ _ _ A w h x y hx hy g hg hxy
  obtain ⟨n, c, rfl⟩ := Unram.exists_diag hx
  obtain ⟨m, d, rfl⟩ := Unram.exists_diag hy
  rw [WD.charPol_mk, WD.charPol_mk, WDRep.diag_ρ, WDRep.diag_ρ, charpoly_diagEnd, charpoly_diagEnd, hg] at hxy
  have key := congrArg Polynomial.roots hxy
  simp only [Finset.prod_eq_multiset_prod] at key
  have R : ∀ {k : ℕ} (e : Fin k → ℂˣ),
      (Multiset.map (fun i => Polynomial.X - Polynomial.C (((e i : ℂˣ) : ℂ) ^ (-1 : ℤ))) Finset.univ.val).prod.roots =
        Finset.univ.val.map fun i => ((e i : ℂˣ) : ℂ) ^ (-1 : ℤ) := by
    intro k e
    have := Polynomial.roots_multiset_prod_X_sub_C
      (Finset.univ.val.map fun i => ((e i : ℂˣ) : ℂ) ^ (-1 : ℤ))
    rwa [Multiset.map_map] at this
  rw [R, R] at key
  apply Unram.diag_eq_diag
  have := congrArg (Multiset.map fun z : ℂ => z⁻¹) key
  simpa [Multiset.map_map, Function.comp_def, zpow_neg_one, inv_inv] using this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PWdModel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem charPol_wdPst {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
    [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (LL : FinExt l)
    {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (hV : IsPst P ρ) (g : ↥(Weil h)) :
    haveI := hV.finite
    (wdPst P ι Bw h hj ρ).charPol g = (wdRho P ι Bw h hj ρ g).charpoly := by
  have := hV.finite
  rw [wdPst_of_isPst ι Bw h hj hV, WD.charPol_mk]
  obtain ⟨u, -, hu, -, hc, hρ⟩ := wdRep_spec P ι Bw h hj ρ
  exact (GlobalTheory.WeilDeligne.isFrobSS_of_unipotent u hu hc hρ).charpoly_eq g

theorem UpperTheory.Gal.crystallineComparison.wdModel_of :
    WdModel := by
  intro l _ P ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj a r LL r' hm hV g
  have key : wdAt P ι Bw h hj r = wdPst P ι Bw h hj (Bw.repE LL r') := by
    obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι Bw h hj (r := r) ⟨LL, r', hm, hV⟩
    have h₁ : L₁.1 ≤ (supExt L₁ LL).1 := le_sup_left
    have h₂ : LL.1 ≤ (supExt L₁ LL).1 := le_sup_right
    have e : mapRep (IntermediateField.inclusion h₁).toRingHom r₁ =
        mapRep (IntermediateField.inclusion h₂).toRingHom r' := by
      ext x i j
      exact congrArg (fun f : ↥(Dec (F := E) A) →* GL (Fin a) (Om l) => (f x : Matrix (Fin a) (Fin a) (Om l)) i j)
        (hm₁.2.trans hm.2.symm)
    rw [e₁, GlobalTheory.Pst.BridgeParam.wdPst_enlarge P ι Bw h hj h₁ r₁ hV₁,
      GlobalTheory.Pst.BridgeParam.wdPst_enlarge P ι Bw h hj h₂ r' hV, e]
  refine ⟨?_, ?_⟩
  · rw [key]
    exact charPol_wdPst P ι h Bw hj LL (Bw.repE LL r') hV g
  · exact (GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι Bw.Kw LL _ _ hV).trans (by simp)
end

