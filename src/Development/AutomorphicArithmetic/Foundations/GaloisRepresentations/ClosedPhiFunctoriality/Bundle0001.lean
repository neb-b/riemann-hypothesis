module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.ColInv
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem actQ_symm {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (g : GQ l)
    (y : Per.Bcris l) : P.actQ g (T.eB.symm y) = T.eB.symm (Per.σB g y) := by
  apply T.eB.injective
  rw [T.actB, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

private theorem phiB_symm {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (y : Per.Bcris l) : P.φB (T.eB.symm y) = T.eB.symm (Per.φB l y) := by
  apply T.eB.injective
  rw [T.frob, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

private theorem smul_symm {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (z : ℤ_[l])
    (y : Per.Bcris l) : (z : ℚ_[l]) • T.eB.symm y = T.eB.symm (Per.zB l z * y) := by
  apply T.eB.injective
  rw [Algebra.smul_def, map_mul, T.zB, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

private theorem smul_Cst {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (z : ℤ_[l])
    (y : Per.Bcris l) : (z : ℚ_[l]) • (Polynomial.C (T.eB.symm y) : Bst P) = Polynomial.C (T.eB.symm (Per.zB l z * y)) := by
  rw [← smul_symm T z y]
  exact Polynomial.smul_C (z : ℚ_[l]) (T.eB.symm y)

private theorem sum_Cst {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {ι : Type}
    (s : Finset ι) (f : ι → Per.Bcris l) :
    ∑ i ∈ s, (Polynomial.C (T.eB.symm (f i)) : Bst P) = Polynomial.C (T.eB.symm (∑ i ∈ s, f i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum T.eB.symm]
  exact (map_sum (Polynomial.C : P.R.B →+* Polynomial P.R.B) _ _).symm

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.colInv_holds :
    ColInv := by
  intro l _ P AI T K L a d ρ R v hv U hU j
  refine ⟨?_, fun n => ?_⟩
  · rw [mem_Dst]
    intro g
    have hinv : ∀ i', ∑ i, Per.zB l ((ρ g).val i' i) * Per.σB (g : GQ l) (U i j) = U i' j := fun i' => by
      have h := congrFun (congrFun (hU.inv g) i') j
      simpa [Matrix.mul_apply, Matrix.map_apply] using h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    have step : ∀ i, (stRep P R g) (v i ⊗ₜ[ℚ_[l]] (Polynomial.C (T.eB.symm (U i j)) : Bst P)) =
        ∑ i', v i' ⊗ₜ[ℚ_[l]] (Polynomial.C (T.eB.symm (Per.zB l ((ρ g).val i' i) * Per.σB (g : GQ l) (U i j))) : Bst P) := fun i => by
      rw [stRep_tmul, actSt_C, actQ_symm T, hv, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [← smul_Cst T, TensorProduct.smul_tmul]
    simp only [step]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [← TensorProduct.tmul_sum, sum_Cst T, hinv]
  · induction n with
    | zero => simp
    | succ n ih =>
      set_option synthInstance.maxHeartbeats 100000 in
        rw [pow_succ', Module.End.mul_apply, ih, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [phiV_tmul, phiSt_C, phiB_symm T, pow_succ', RingHom.mul_def, RingHom.comp_apply]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.CoordEx
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

variable {l : ℕ} [Fact l.Prime]

private def coordPair (P : LocPrime l) (L : FinExt l) (a : ℕ) :
    (Fin a → ↥L.1) →+ Bst P →+ (Fin a → OB P) :=
  AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (fun b i => ((v i : ↥L.1) : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)] b)
      (fun b b' => by funext i; simp [TensorProduct.tmul_add]))
    (fun v v' => by
      ext b i
      simp [TensorProduct.add_tmul])

theorem coordEx_holds : CoordEx := by
  intro l _ P L a
  refine ⟨TensorProduct.liftAddHom (coordPair P L a) ?_, ?_⟩
  · intro r v b
    funext i
    simp only [coordPair, AddMonoidHom.mk'_apply, Pi.smul_apply]
    rw [show ((r • v i : ↥L.1) : Om l) = r • ((v i : ↥L.1) : Om l) from rfl]
    exact TensorProduct.smul_tmul r _ b
  · intro v b i
    rfl

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.CoordWD
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem letter_lift {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D]
    (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F)
    {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (κ : F →+* B) (f : D →+ M)
    (hL : ∀ (r : LL) (x : D), f (r • x) = κ (algebraMap LL F r) • f x)
    (hU : ∀ (u : U) (x : D), f (m u x) = κ (τ u) • f x) :
    ∃ ψ : Letter m F τ →+ M, (∀ (c : F) (y : Letter m F τ), ψ (c • y) = κ c • ψ y) ∧
      ∀ x : D, ψ (letterMk m F τ x) = f x := by
  letI : Module F M := Module.compHom M κ
  have hsm : ∀ (c : F) (y : M), c • y = κ c • y := fun _ _ => rfl
  let f₂ : F →+ D →+ M := AddMonoidHom.mk' (fun c =>
      (DistribSMul.toAddMonoidHom M (κ c)).comp f)
    (fun c c' => by
      ext x
      simp [add_smul])
  have hf₂ : ∀ c x, f₂ c x = κ c • f x := fun _ _ => rfl
  let g : F ⊗[LL] D →+ M := TensorProduct.liftAddHom f₂ fun r c x => by
    rw [hf₂, hf₂, hL, Algebra.smul_def, map_mul, mul_comm, mul_smul, smul_comm]
  have hg : ∀ c x, g (c ⊗ₜ x) = κ c • f x := fun _ _ => rfl
  have hgs : ∀ (c : F) (y : F ⊗[LL] D), g (c • y) = κ c • g y := fun c y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), smul_add, hx, hy]
    | tmul c' x => rw [TensorProduct.smul_tmul', hg, hg, smul_eq_mul, map_mul, mul_smul]
  let gL : F ⊗[LL] D →ₗ[F] M := { toFun := g, map_add' := g.map_add, map_smul' := hgs }
  have hk : letterKer m F τ ≤ LinearMap.ker gL := iSup_le fun u => by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    change g _ = 0
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
    | tmul c x =>
      simp only [LinearMap.sub_apply, LinearMap.baseChange_tmul, LinearMap.smul_apply, LinearMap.id_apply,
        map_sub, hgs, hg, hU]
      rw [smul_comm, sub_self]
  let ψL : Letter m F τ →ₗ[F] M := (letterKer m F τ).liftQ gL hk
  refine ⟨ψL.toAddMonoidHom, fun c y => ψL.map_smul c y, fun x => ?_⟩
  change g (1 ⊗ₜ x) = f x
  rw [hg, map_one, one_smul]

private theorem coord_smul {l : ℕ} [Fact l.Prime] {P : LocPrime l} {L : FinExt l} {a : ℕ}
    {ψ₀ : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P →+ (Fin a → OB P)} (h : IsCoord P L ψ₀) (c : ↥L.1)
    (y : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    ψ₀ (c • y) = (((c : Om l) ⊗ₜ 1 : OB P)) • ψ₀ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), smul_add, hx, hy]
  | tmul v b =>
    funext i
    rw [TensorProduct.smul_tmul', h, Pi.smul_apply, Pi.smul_apply, h, smul_eq_mul, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl

private theorem coord_mulV {l : ℕ} [Fact l.Prime] {P : LocPrime l} {L : FinExt l} {a : ℕ}
    {ψ₀ : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P →+ (Fin a → OB P)} (h : IsCoord P L ψ₀) (c : ↥(MaximalUnramifiedExtension l))
    (y : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    ψ₀ (GlobalTheory.Pst.mulV P ↥L.1 (Fin a → ↥L.1) c y) = (((c : Om l) ⊗ₜ 1 : OB P)) • ψ₀ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), smul_add, hx, hy]
  | tmul v b =>
    funext i
    rw [GlobalTheory.Pst.mulV_tmul, h, Pi.smul_apply, h, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul]
    rfl

private noncomputable def kap {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) : ℂ →+* OB P :=
  (Algebra.TensorProduct.includeLeftRingHom : Om l →+* OB P).comp ι.symm.toRingHom

private theorem kap_apply {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) (z : Om l) :
    kap P ι (ι z) = (z ⊗ₜ 1 : OB P) := by
  change ((ι.symm (ι z) ⊗ₜ 1 : OB P)) = _
  rw [RingEquiv.symm_apply_apply]

section
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K L : FinExt l} {a : ℕ}
  (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1))
  (ψ₀ : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P →+ (Fin a → OB P))


set_option synthInstance.maxHeartbeats 400000 in
private noncomputable def fD : ↥(GlobalTheory.Pst.Dpst P R) →+ (Fin a → OB P) :=
  { toFun := fun x => ψ₀ x.1, map_zero' := ψ₀.map_zero, map_add' := fun x y => ψ₀.map_add x.1 y.1 }

set_option synthInstance.maxHeartbeats 400000 in
private theorem fD_smul (h : IsCoord P L ψ₀) (ι : Om l ≃+* ℂ) (r : ↥L.1) (x : ↥(GlobalTheory.Pst.Dpst P R)) :
    fD R ψ₀ (r • x) = kap P ι (ι (r : Om l)) • fD R ψ₀ x := by
  exact (coord_smul h r x.1).trans
    (congrArg (fun t : OB P => t • ψ₀ x.1) (kap_apply P ι (r : Om l)).symm)

set_option synthInstance.maxHeartbeats 400000 in
private theorem fD_mul (h : IsCoord P L ψ₀) (ι : Om l ≃+* ℂ) (u : ↥(MaximalUnramifiedExtension l)) (x : ↥(GlobalTheory.Pst.Dpst P R)) :
    fD R ψ₀ (GlobalTheory.Pst.mulD P R u x) = kap P ι (ι (u : Om l)) • fD R ψ₀ x := by
  exact (coord_mulV h u x.1).trans
    (congrArg (fun t : OB P => t • ψ₀ x.1) (kap_apply P ι (u : Om l)).symm)

end

set_option synthInstance.maxHeartbeats 400000 in
theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.coordWD_holds :
    CoordWD := by
  intro l _ P ι K L a R ψ₀ h
  obtain ⟨ψ, h1, h2⟩ := @letter_lift ↥L.1 ↥(MaximalUnramifiedExtension l) ↥(GlobalTheory.Pst.Dpst P R) _ _ _ _ (GlobalTheory.Pst.mulD P R) ℂ _ (GlobalTheory.Pst.algC ι L)
    (GlobalTheory.Pst.urC ι) (OB P) (Fin a → OB P) _ _ _ (kap P ι) (fD R ψ₀)
    (fun r x => fD_smul R ψ₀ h ι r x) (fun u x => fD_mul R ψ₀ h ι u x)
  exact ⟨ψ, h1, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.CoverJ
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix GlobalTheory.TraceConjugationCover
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem coverJ_holds : CoverJ := by
  intro l _ Γ _ _ _ _ a L₀ r hr hss Cl hCl p θ hap
  classical
  obtain ⟨d, ρ, b, e, hρ, hreads, hind, hbr⟩ := _root_.GlobalTheory.BKLim.exists_zl_span_lattice_reads l Γ a r hr
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.smallTrace_dvd_span l Γ a r hr hss
  obtain ⟨K, hK⟩ := traceL l a d b
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith

  have hch : ∀ ρ' : Γ →* GL (Fin a) (Om l), ∃ (L : FinExt l) (t : Finset (Matrix (Fin a) (Fin a) (Om l))), Continuous ρ' →
      (L₀.1 ≤ L.1 ∧ (∀ g i j, ((ρ' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1) ∧ (∀ x ∈ t, ∀ i j, x i j ∈ L.1) ∧
        (∀ x : Matrix (Fin a) (Fin a) (Om l), (∀ i j, x i j ∈ L.1) → x ∈ Submodule.span ℚ_[l] (t : Set (Matrix (Fin a) (Fin a) (Om l)))) ∧
        (∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t, zOm l (c' y) • y = 1) ∧
        ∀ g, ∀ x ∈ t, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρ' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t, zOm l (c' y) • y) := by
    intro ρ'
    by_cases h : Continuous ρ'
    · obtain ⟨L, hLf, hL⟩ := _root_.GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem_of_continuous l Γ a ρ' h
      haveI := hLf
      haveI := L₀.2
      let L' : FinExt l := ⟨L ⊔ L₀.1, inferInstance⟩
      have hL' : ∀ g i j, ((ρ' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L'.1 := fun g i j =>
        (le_sup_left : L ≤ L ⊔ L₀.1) (hL g i j)
      obtain ⟨t, h1, h2, h3, h4⟩ := _root_.GlobalTheory.exists_stable_spanning_finset l Γ a ρ' L' h hL'
      exact ⟨L', t, fun _ => ⟨le_sup_right, hL', h1, h2, h3, h4⟩⟩
    · exact ⟨L₀, ∅, fun h' => absurd h' h⟩
  choose Lf tf htf using hch

  have hap' : ∀ n : ℕ, ∃ (s : Finset (Γ →* GL (Fin a) (Om l))) (cc : (Γ →* GL (Fin a) (Om l)) → Om l),
      (s : Set (Γ →* GL (Fin a) (Om l))) ⊆ Cl ∧ (∀ g, ‖trc r g - ∑ ρ' ∈ s, cc ρ' * trc ρ' g‖ ≤ ((l : ℝ)⁻¹) ^ (n + K + c)) ∧
        ‖θ - ∑ ρ' ∈ s, cc ρ' * p ρ'‖ ≤ ((l : ℝ)⁻¹) ^ (n + K + c) :=
    fun n => hap _ (by positivity)
  choose s cc hsCl hscc hth using hap'
  let U : ℕ → Finset (Γ →* GL (Fin a) (Om l)) := fun n => (Finset.range (n + 1)).biUnion s
  have hUmono : ∀ n, U n ⊆ U (n + 1) := fun n =>
    Finset.biUnion_subset_biUnion_of_subset_left _ (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
  have hsU : ∀ n, s n ⊆ U n := fun n => Finset.subset_biUnion_of_mem s (Finset.mem_range.2 (Nat.lt_succ_self n))
  have hUCl : ∀ n, ∀ ρ' ∈ U n, ρ' ∈ Cl := by
    intro n ρ' h
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 h
    exact hsCl j hj
  let m : ℕ → ℕ := fun n => (U n).card
  let ρs : ∀ n, Fin (m n) → (Γ →* GL (Fin a) (Om l)) := fun n k => ((U n).equivFin.symm k).1
  have hρsU : ∀ n k, ρs n k ∈ U n := fun n k => ((U n).equivFin.symm k).2
  have hρsC : ∀ n k, Continuous (ρs n k) := fun n k => hCl _ (hUCl n _ (hρsU n k))
  let cs : ∀ n, Fin (m n) → Om l := fun n k => if ρs n k ∈ s n then cc n (ρs n k) else 0
  have hcs : ∀ n (q : (Γ →* GL (Fin a) (Om l)) → Om l), ∑ k, cs n k * q (ρs n k) = ∑ ρ' ∈ s n, cc n ρ' * q ρ' := by
    intro n q
    have e1 : ∑ k, cs n k * q (ρs n k) = ∑ x : (U n), (if x.1 ∈ s n then cc n x.1 else 0) * q x.1 :=
      Fintype.sum_equiv (U n).equivFin.symm _ _ (fun k => rfl)
    rw [e1, Finset.sum_coe_sort (U n) (fun x => (if x ∈ s n then cc n x else 0) * q x)]
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (hsU n)]
  have hK' : ∀ n, ∀ w : Fin d → ℤ_[l], ‖((l : Om l) ^ (n + K) • ∑ i, zOm l (w i) • b i).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
    intro n w
    rw [Matrix.trace_smul, smul_eq_mul, norm_mul, norm_pow, norm_l]
    calc ((l : ℝ)⁻¹) ^ (n + K) * ‖(∑ i, zOm l (w i) • b i).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + K) * (l : ℝ) ^ K :=
          mul_le_mul_of_nonneg_left (hK w) (by positivity)
      _ = ((l : ℝ) ^ n)⁻¹ := by
          rw [pow_add, inv_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
  have hlay : ∀ n, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∃ (d' : ℕ) (ρ' : Γ →* GL (Fin d') ℤ_[l]) (bb : Fin d' → Fin (m n) → Matrix (Fin a) (Fin a) (Om l)) (e' : Fin d' → ℤ_[l]) (P : Matrix (Fin d) (Fin d') ℤ_[l]), Continuous ρ' ∧ (∀ s k i j, bb s k i j ∈ (Lf (ρs n k)).1) ∧ LinearIndependent ℚ_[l] bb ∧ (∀ x : Fin (m n) → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (Lf (ρs n k)).1) → x ∈ Submodule.span ℚ_[l] (Set.range bb)) ∧ (∀ k, Reads ρ' (ρs n k) (fun s => bb s k) e') ∧ (∀ s, bb s ∈ latT (ρs n) (fun k => tf (ρs n k)) M) ∧ (∀ x ∈ latT (ρs n) (fun k => tf (ρs n k)) M, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s) ∧ Carries r b (ρs n) (fun k => tf (ρs n k)) M bb P (n + K) ∧ Onto (fun g => ((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l])) (fun g => ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l])) P n ∧ (∀ i, (l : ℤ_[l]) ^ n ∣ (P *ᵥ e' - e) i) ∧ ∀ s, ‖(∑ i, zOm l (P i s) • b i).trace - ∑ k, cs n k * (bb s k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
    intro n
    exact GlobalTheory.T.exists_lattice_layer_cover_basis_mod_pow l Γ a r d ρ b e hreads hind hbr c hc n (n + K) (by omega) (hK' n) (m n) (ρs n)
      (fun k => Lf (ρs n k)) (fun k => tf (ρs n k)) (hρsC n) (fun k => (htf _ (hρsC n k)).2.1)
      (fun k => (htf _ (hρsC n k)).2.2.1) (fun k => (htf _ (hρsC n k)).2.2.2.1)
      (fun k => (htf _ (hρsC n k)).2.2.2.2.1) (fun k => (htf _ (hρsC n k)).2.2.2.2.2) (cs n)
      (fun g => by rw [hcs n (fun ρ' => trc ρ' g)]; exact hscc n g)
  choose M₀ hM₀ using hlay
  let M : ℕ → ℕ := fun n => ∑ j ∈ Finset.range (n + 1), M₀ j
  have hMle : ∀ n, M₀ n ≤ M n := fun n =>
    Finset.single_le_sum (f := M₀) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_self n))
  have hMmono : ∀ n, M n ≤ M (n + 1) := fun n => by
    simp only [M]
    rw [Finset.sum_range_succ _ (n + 1)]
    exact Nat.le_add_right _ _
  have hL := fun n => hM₀ n (M n) (hMle n)
  choose d' ρ' bb e' P hcont hbbL hind' hspan' hreads' hmem hcoord hcar honto hunit htr using hL
  let ι : ∀ n, Fin (m n) → Fin (m (n + 1)) := fun n k =>
    (U (n + 1)).equivFin ⟨((U n).equivFin.symm k).1, hUmono n ((U n).equivFin.symm k).2⟩
  have hι : ∀ n k, ρs (n + 1) (ι n k) = ρs n k := by
    intro n k
    simp [ρs, ι]
  have htrans : ∀ n, ∃ f : Matrix (Fin (d' n)) (Fin (d' (n + 1))) ℤ_[l], (∀ g, f * ((ρ' (n + 1) g : GL (Fin (d' (n + 1))) ℤ_[l]) : Matrix (Fin (d' (n + 1))) (Fin (d' (n + 1))) ℤ_[l]) = ((ρ' n g : GL (Fin (d' n)) ℤ_[l]) : Matrix (Fin (d' n)) (Fin (d' n)) ℤ_[l]) * f) ∧ ∀ i j, (l : ℤ_[l]) ^ n ∣ (P n * f - P (n + 1)) i j := by
    intro n
    exact GlobalTheory.T.exists_equivariant_transition_matrix_cover l Γ a r d b hind (m n) (m (n + 1)) (ρs n) (ρs (n + 1)) (ι n) (hι n)
      (fun k => tf (ρs n k)) (fun k => tf (ρs (n + 1) k)) (fun k => by rw [hι n k]) (M n) (M (n + 1)) (hMmono n)
      (d' n) (d' (n + 1)) (ρ' n) (ρ' (n + 1)) (bb n) (bb (n + 1)) (e' n) (e' (n + 1)) (hind' n) (hreads' n)
      (hreads' (n + 1)) (hmem (n + 1)) (hcoord n) (P n) (P (n + 1)) n (n + K) (n + 1 + K) (by omega) (by omega)
      (hcar n) (hcar (n + 1))
  choose f hfe hfP using htrans
  let tw : Tower ρ :=
    { d' := d', ρ' := ρ', Pi := P, onto := honto, f := f, f_equi := hfe, f_Pi := hfP }
  let lay : ∀ n, Layer L₀ Cl (tw.ρ' n) := fun n =>
    { m := m n, rep := ρs n, mem := fun k => hUCl n _ (hρsU n k), L := fun k => Lf (ρs n k),
      le := fun k => (htf _ (hρsC n k)).1, rep_mem := fun k => (htf _ (hρsC n k)).2.1, b := bb n,
      b_mem := hbbL n, indep := hind' n, span := hspan' n, e := e' n, reads := hreads' n, c := cs n }
  refine ⟨{ d := d, ρ := ρ, cont := hρ, b := b, e := e, reads := hreads, tw := tw, cont' := hcont, lay := lay,
            unit := hunit, trace := htr }, fun n => ?_⟩
  show ‖θ - ∑ k, cs n k * p (ρs n k)‖ ≤ _
  rw [hcs n p]
  refine (hth n).trans ?_
  rw [← inv_pow]
  exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hl1.le) (by omega)

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.DvdMulEntriesRight
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem map_smul_ringHom {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) {d : ℕ} (c : S)
    (M : Matrix (Fin d) (Fin d) S) : (c • M).map f = f c • M.map f := by
  ext i j; simp

private theorem dvd_mul_entries_left {T : Type} [CommRing T] {a b e : ℕ} (c : T) (A : Matrix (Fin a) (Fin b) T)
    (B : Matrix (Fin b) (Fin e) T) (h : ∀ i j, c ∣ B i j) (i : Fin a) (j : Fin e) : c ∣ (A * B) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (h k j) _

private theorem dvd_mul_entries_right {T : Type} [CommRing T] {a b e : ℕ} (c : T) (A : Matrix (Fin a) (Fin b) T)
    (B : Matrix (Fin b) (Fin e) T) (h : ∀ i j, c ∣ A i j) (i : Fin a) (j : Fin e) : c ∣ (A * B) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_right (h i k) _

private theorem map_intertwine {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (ψ : S →+* S) (φ : T →+* T)
    (hf : ∀ s, φ (f s) = f (ψ s)) {d d' : ℕ} (c : S) (A : Matrix (Fin d) (Fin d) S) (A₁ : Matrix (Fin d') (Fin d') S)
    (R : Matrix (Fin d) (Fin d') S) (h : ∀ i j, c ∣ (R * A₁ - A * R.map ψ) i j) (i : Fin d) (j : Fin d') :
    f c ∣ (R.map f * A₁.map f - A.map f * (R.map f).map φ) i j := by
  have e : R.map f * A₁.map f - A.map f * (R.map f).map φ = (R * A₁ - A * R.map ψ).map f := by
    have e' : (R.map f).map φ = (R.map ψ).map f := by
      ext i j; simp [hf]
    rw [e']
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, map_sum]
  rw [e, Matrix.map_apply]
  exact map_dvd f (h i j)

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.linkQ_holds :
    ZeroAp → LinkRec → LinkQ := by
  intro hZ hR l _ K bk N M
  obtain ⟨n, hn⟩ := hZ l K bk (3 * N) M
  refine ⟨n, ?_⟩
  intro k d d' A A₁ A₁' Q Q' Q₁ Q₁' R hA hS hS₁ hRel
  obtain ⟨-, -, ⟨v, hv⟩, hφι, -⟩ := _root_.GlobalTheory.AcrisFrobE.main l K bk
  have hv' : fA bk bk.E = (l : Per.Acris l) * v := hv
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : (Per.Acris l)ˣ, f0 bk bk.E = (l : Per.Acris l) * w₀ := by
    obtain ⟨w, hw⟩ := bk.coeff_zero
    have hc : PowerSeries.constantCoeff bk.E = (l : Wq l bk.a) * w := by
      rw [← hw]; simp
    refine ⟨(Units.map (PowerSeries.C (R := Wq l bk.a)).toMonoidHom w).map (fA bk).toMonoidHom, ?_⟩
    simp [f0, hc]
  have hφA : ∀ s, phiA l (fA bk s) = fA bk (frobS l bk.a s) := fun s => by
    simp only [fA, RingHom.comp_apply, hφι, bk.ev_frob]
  have hφ0 : ∀ s, phiA l (f0 bk s) = f0 bk (frobS l bk.a s) := fun s => by
    rw [show f0 bk s = fA bk (PowerSeries.C (PowerSeries.constantCoeff s)) from rfl, hφA, frobS_C,
      show f0 bk (frobS l bk.a s) = fA bk (PowerSeries.C (PowerSeries.constantCoeff (frobS l bk.a s))) from rfl,
      constantCoeff_frobS_apply]
  have hdiff : ∀ s, uC bk ∣ fA bk s - f0 bk s := fun s => by
    obtain ⟨t, ht⟩ := (PowerSeries.X_dvd_iff (φ := s - PowerSeries.C (PowerSeries.constantCoeff s))).2 (by simp)
    have e : fA bk s - f0 bk s = uC bk ^ l * fA bk t := by
      rw [show f0 bk s = fA bk (PowerSeries.C (PowerSeries.constantCoeff s)) from rfl, ← map_sub, ht, map_mul]
      congr 1
      simp [fA, uC, frobS_X]
    rw [e]
    exact Dvd.dvd.mul_right (dvd_pow_self _ (Fact.out : l.Prime).ne_zero) _
  have hlc : ∀ f : bk.S →+* Per.Acris l, f ((l : bk.S) ^ n) = (l : Per.Acris l) ^ n := fun f => by
    rw [map_pow, map_natCast]
  have h1 : A₁.map (f0 bk) * A₁'.map (f0 bk) =
      ((l : Per.Acris l) * w₀) ^ (2 * N) • (1 : Matrix (Fin d') (Fin d') (Per.Acris l)) := by
    rw [← hw₀, ← Matrix.map_mul, hA, map_smul_ringHom, map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : ((l : Per.Acris l) * v) ^ N • (Q * A.map (f0 bk)) =
      ((l : Per.Acris l) * w₀) ^ N • (A.map (fA bk) * Q.map (phiA l)) := by
    rw [← hv', ← hw₀]; exact hS.frob
  have h3 : ((l : Per.Acris l) * v) ^ N • (Q₁ * A₁.map (f0 bk)) =
      ((l : Per.Acris l) * w₀) ^ N • (A₁.map (fA bk) * Q₁.map (phiA l)) := by
    rw [← hv', ← hw₀]; exact hS₁.frob
  have h4 : ∀ i j, (l : Per.Acris l) ^ n ∣
      (R.map (fA bk) * A₁.map (fA bk) - A.map (fA bk) * (R.map (fA bk)).map (phiA l)) i j := fun i j => by
    rw [← hlc (fA bk)]
    exact map_intertwine (fA bk) (frobS l bk.a) (phiA l) hφA _ A A₁ R hRel i j
  have h5 : ∀ i j, (l : Per.Acris l) ^ n ∣
      (R.map (f0 bk) * A₁.map (f0 bk) - A.map (f0 bk) * (R.map (f0 bk)).map (phiA l)) i j := fun i j => by
    rw [← hlc (f0 bk)]
    exact map_intertwine (f0 bk) (frobS l bk.a) (phiA l) hφ0 _ A A₁ R hRel i j
  obtain ⟨F, F', hF⟩ := hR (Per.Acris l) (phiA l) (l : Per.Acris l) ((l : Per.Acris l) ^ n) v w₀ N d d'
    (A.map (fA bk)) (A.map (f0 bk)) Q (A₁.map (fA bk)) (A₁.map (f0 bk)) (A₁'.map (f0 bk)) Q₁
    (R.map (fA bk)) (R.map (f0 bk)) h1 h2 h3 h4 h5
  refine hn d d' _ F F' ?_ hF
  intro i j
  have hD : R.map (fA bk) * Q₁ - Q * R.map (f0 bk) =
      R.map (fA bk) * (Q₁ - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d') (Fin d') (Per.Acris l))) +
        (l : Per.Acris l) ^ k • (R.map (fA bk) - R.map (f0 bk)) -
        (Q - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) * R.map (f0 bk) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_sub]
    abel
  rw [hD, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply]
  refine dvd_sub (dvd_add (dvd_mul_entries_left _ _ _ hS₁.mod i j) ?_) (dvd_mul_entries_right _ _ _ hS.mod i j)
  rw [smul_eq_mul]
  exact Dvd.dvd.mul_left (hdiff _) _
end

