module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.OrthogonalInvarianceOfStableRankOne
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachModuleOfXPowSmulFrobeniusGamma
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0379

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightLowerComparison
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.LowerWt

theorem coeff_mul_eSerC {g : ℕ} [Fact g.Prime] (L : LabelDatum g) {N : ℕ} (f : (ZMod g)[X])
    (a : MonoidAlgebra ℂ (Gn g N))
    (hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite) :
    (a * eSerC L N f).coeff 1 = ∑ χ ∈ hfin.toFinset, χ 1 / (Fintype.card (Gn g N) : ℂ) * tr a χ := by
  unfold eSerC
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun χ _ => ?_
  exact ((GlobalTheory.GLq.trIdem (Gn g N) a χ).2.2)

theorem re_coeff_mul_eSerC {g : ℕ} [Fact g.Prime] (L : LabelDatum g) {N : ℕ} (f : (ZMod g)[X])
    (a : MonoidAlgebra ℂ (Gn g N))
    (hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite) :
    ((a * eSerC L N f).coeff 1).re =
      ∑ χ ∈ hfin.toFinset, (χ 1).re / (Fintype.card (Gn g N) : ℝ) * (tr a χ).re := by
  rw [coeff_mul_eSerC L f a hfin, Complex.re_sum]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have hI : IsIrr χ := ((Set.Finite.mem_toFinset hfin).1 hχ).1
  obtain ⟨d, -, hd⟩ := (GlobalTheory.GLq.trIdem (Gn g N) a χ).2.1 hI
  rw [hd]
  have : (d : ℂ) / (Fintype.card (Gn g N) : ℂ) = (((d : ℝ) / (Fintype.card (Gn g N) : ℝ) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [this, Complex.re_ofReal_mul]
  simp

theorem weight_nonneg {g : ℕ} [Fact g.Prime] (L : LabelDatum g) {N : ℕ} (f : (ZMod g)[X])
    (hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite) (χ : Gn g N → ℂ) (hχ : χ ∈ hfin.toFinset) :
    0 ≤ (χ 1).re / (Fintype.card (Gn g N) : ℝ) := by
  have hI : IsIrr χ := ((Set.Finite.mem_toFinset hfin).1 hχ).1
  obtain ⟨d, -, hd⟩ := (GlobalTheory.GLq.trIdem (Gn g N) (1 : MonoidAlgebra ℂ (Gn g N)) χ).2.1 hI
  rw [hd]
  simp only [Complex.natCast_re]
  positivity

end GlobalTheory.GLq.LowerWt

theorem GlobalTheory.GLq.lowerWtComparison : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 →
    ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k →
      ∀ f, (1 - 1 / (g : ℝ)) * wtC L (eU g N ψ) f ≤ wtC L (eJ g N k s ψ) f := by
  intro g _ L ψ hψ N k s hN hk f
  have hL8 := _root_.GlobalTheory.GLq.MirabolicComparison.mirabolic_comparison g ψ hψ N k s hN hk
  obtain ⟨-, hU1, hJ, -⟩ := _root_.GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField g N k s ψ
  obtain ⟨-, hJ1⟩ := hJ hN
  have hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite :=
    (irr_finite_and_finsum_zOf_eq_one (Gn g N)).1.subset fun χ h => h.1
  set T := hfin.toFinset
  set c : (Gn g N → ℂ) → ℝ := fun χ => (χ 1).re / (Fintype.card (Gn g N) : ℝ) with hc
  set A := ∑ χ ∈ T, c χ * (tr (eU g N ψ) χ).re with hA
  set B := ∑ χ ∈ T, c χ * (tr (eJ g N k s ψ) χ).re with hB
  have hAeq : ((eU g N ψ * eSerC L N f).coeff 1).re = A := LowerWt.re_coeff_mul_eSerC L f _ hfin
  have hBeq : ((eJ g N k s ψ * eSerC L N f).coeff 1).re = B := LowerWt.re_coeff_mul_eSerC L f _ hfin
  have hG : (0 : ℝ) < g := by exact_mod_cast (Fact.out : g.Prime).pos
  set M := N * (N - 1) / 2
  have hU1r : ((eU g N ψ).coeff 1).re = ((g : ℝ) ^ M)⁻¹ := by
    rw [hU1]
    have : ((g : ℂ) ^ M)⁻¹ = ((((g : ℝ) ^ M)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_re]
  have hJ1r : ((eJ g N k s ψ).coeff 1).re = (g : ℝ) ^ k * ((g : ℝ) ^ M)⁻¹ := by
    rw [hJ1]
    have : (g : ℂ) ^ k * ((g : ℂ) ^ M)⁻¹ = ((((g : ℝ) ^ k * ((g : ℝ) ^ M)⁻¹) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_re]
  have hBA : ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * A ≤ B := by
    rw [hA, hB, Finset.mul_sum]
    refine Finset.sum_le_sum fun χ hχ => ?_
    have h0 : 0 ≤ c χ := LowerWt.weight_nonneg L f hfin χ hχ
    have hI : IsIrr χ := ((Set.Finite.mem_toFinset hfin).1 hχ).1
    have hC : IsChar χ := by obtain ⟨V, -, hV⟩ := hI; exact ⟨V, hV⟩
    have h8 := hL8 χ hC
    unfold wh at h8
    calc ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (c χ * (tr (eU g N ψ) χ).re)
        = c χ * (((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (tr (eU g N ψ) χ).re) := by ring
      _ ≤ c χ * (tr (eJ g N k s ψ) χ).re := mul_le_mul_of_nonneg_left h8 h0
  have hpow : (g : ℝ) ^ k - (g : ℝ) ^ (k - 1) = (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp
  unfold wtC
  rw [hAeq, hBeq, hU1r, hJ1r]
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := pow_pos hG k
  have hgM : (0 : ℝ) < (g : ℝ) ^ M := pow_pos hG M
  rw [hpow] at hBA
  rw [div_inv_eq_mul, le_div_iff₀ (mul_pos hgk (inv_pos.2 hgM))]
  calc (1 - 1 / (g : ℝ)) * (A * (g : ℝ) ^ M) * ((g : ℝ) ^ k * ((g : ℝ) ^ M)⁻¹)
      = (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) * A * ((g : ℝ) ^ M * ((g : ℝ) ^ M)⁻¹) := by ring
    _ = (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) * A := by rw [mul_inv_cancel₀ hgM.ne', mul_one]
    _ ≤ B := hBA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantPhiSolutionMemOE
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem invariant_phi_solution_approx (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ]
    (c : κ → κ → WCb l) (hc : ∀ i j, c i j ∈ bk.OE) (n : ℕ) :
    ∀ (x b : κ → WCb l), (∀ j, b j ∈ bk.OE) → (∀ j, x j = ∑ i, frobW l (x i) * c i j + b j) →
      (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x j) = x j) →
      ∀ j, ∃ v ∈ bk.OE, ((l : ℕ) : WCb l) ^ n ∣ x j - v := by
  induction n with
  | zero => exact fun x b _ _ _ j => ⟨0, bk.OE.zero_mem, by simp⟩
  | succ n ih =>
    intro x b hb hx hg j
    obtain ⟨v, x', b', hv, hb', hxv, hx', hg'⟩ := _root_.GlobalTheory.BSP.BK.descent_step l K bk κ x b c hc hb hx hg
    obtain ⟨v', hv', y, hy⟩ := ih x' b' hb' hx' hg' j
    refine ⟨v j + ((l : ℕ) : WCb l) * v', bk.OE.add_mem (hv j) (bk.OE.mul_mem (natCast_mem bk.OE l) hv'), y, ?_⟩
    rw [hxv j]
    linear_combination ((l : ℕ) : WCb l) * hy

theorem invariant_phi_solution_mem_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ]
    (x : κ → WCb l) (c : κ → κ → WCb l), (∀ i j, c i j ∈ bk.OE) → (∀ j, x j = ∑ i, frobW l (x i) * c i j) →
    (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x j) = x j) → ∀ j, x j ∈ bk.OE := by
  intro l _ K bk κ _ x c hc hx hg j
  refine (_root_.GlobalTheory.OEStable.main l K bk).2.1 (x j) fun n => ?_
  exact invariant_phi_solution_approx l K bk κ c hc n x (fun _ => 0) (fun _ => bk.OE.zero_mem)
    (fun j => by rw [add_zero]; exact hx j) hg j

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsComplementedSubrepLocalMatrixRepTwistedSum
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section
namespace GlobalTheory.Pass.LocDual.Summand

theorem exists_left_inv {K : Type} [Field K] {Γ : Type} [Group Γ] {n k : ℕ}
    (A : Γ → Matrix (Fin n) (Fin n) K) (j : (Fin k → K) →ₗ[K] (Fin n → K)) (hinj : Function.Injective j)
    (W' : Submodule K (Fin n → K)) (hc : IsCompl (LinearMap.range j) W')
    (hW : ∀ g, ∀ v ∈ LinearMap.range j, (A g).mulVec v ∈ LinearMap.range j)
    (hW' : ∀ g, ∀ v ∈ W', (A g).mulVec v ∈ W') :
    ∃ Bl : (Fin n → K) →ₗ[K] (Fin k → K), (∀ u, Bl (j u) = u) ∧
      ∀ g v, j (Bl ((A g).mulVec v)) = (A g).mulVec (j (Bl v)) := by
  let e := LinearEquiv.ofInjective j hinj
  let P := Submodule.linearProjOfIsCompl (LinearMap.range j) W' hc
  have hjB : ∀ v, j ((e.symm.toLinearMap ∘ₗ P) v) = (P v : Fin n → K) := by
    intro v
    have := congrArg Subtype.val (e.apply_symm_apply (P v))
    simpa [e, LinearEquiv.ofInjective_apply] using this
  have hP : ∀ v, ∀ a ∈ LinearMap.range j, ∀ b ∈ W', v = a + b → (P v : Fin n → K) = a := by
    intro v a ha b hb hv
    subst hv
    have h1 : P a = ⟨a, ha⟩ := Submodule.linearProjOfIsCompl_apply_left hc ⟨a, ha⟩
    have h2 : P b = 0 := Submodule.linearProjOfIsCompl_apply_right hc ⟨b, hb⟩
    rw [map_add (f := _), Submodule.coe_add, h1, h2]
    simp
  refine ⟨e.symm.toLinearMap ∘ₗ P, ?_, ?_⟩
  · intro u
    apply hinj
    rw [hjB]
    exact hP _ _ ⟨u, rfl⟩ 0 W'.zero_mem (by simp)
  · intro g v
    have hv : v ∈ LinearMap.range j ⊔ W' := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [hjB, hjB, hP (a + b) a ha b hb rfl, hP _ _ (hW g a ha) _ (hW' g b hb) (Matrix.mulVec_add _ _ _)]

theorem loc_eq (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (g : Br.G D.nbr i w hw) :
    Br.loc D.nbr i w hw M g =
      (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).map (Br.toLLK (D.nbr i w hw)) := by
  refine Matrix.ext fun a b => ?_
  change (D.nbr i w hw).toLL (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b) =
    Br.toLLK (D.nbr i w hw) (toK D.nd i (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b))
  rw [Br.toLLK_alg]
  rfl

theorem twist_eq (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (x : D.nd.X i) (g : GE D.nd) :
    mapM (toK D.nd i) (rTwO D.nd i r x) g =
      toK D.nd i ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) •
        ((mapRep (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) (r x) g : GL (Fin D.R.nV) (FractionRing (D.nd.O i))) :
          Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) := by
  refine Matrix.ext fun a b => ?_
  change toK D.nd i (((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) * ((r x g : GL _ _) : Matrix _ _ _) a b) =
    toK D.nd i ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) * toK D.nd i (((r x g : GL _ _) : Matrix _ _ _) a b)
  exact map_mul _ _ _

end GlobalTheory.Pass.LocDual.Summand


open GlobalTheory.Pass.LocDual.Summand in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.Pass.LocDual.isSummandTw_locU : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M),
      IsSummandTw i w hw r Xs (locU i w hw M hSub.1) := by
  intro D i r hr Xs w hw k M hSub
  obtain ⟨x, hx, j, hinj, hj⟩ := hSub.2
  let K := FractionRing (D.nd.O i)
  let A : GE D.nd → Matrix (Fin D.R.nV) (Fin D.R.nV) K := fun g => mapM (toK D.nd i) (rTwO D.nd i r x) g
  let Rm : GE D.nd → Matrix (Fin D.R.nV) (Fin D.R.nV) K := fun g =>
    ((mapRep (algebraMap (D.nd.O i) K) (r x) g : GL (Fin D.R.nV) K) : Matrix (Fin D.R.nV) (Fin D.R.nV) K)
  let c : GE D.nd → Kˣ := fun g => Units.map (toK D.nd i).toMonoidHom ((chiU D.nd i 1)⁻¹ g)
  have hA : ∀ g, A g = ((c g : Kˣ) : K) • Rm g := fun g => twist_eq D i r x g
  have hR : ∀ g v, (Rm g).mulVec v = (((c g)⁻¹ : Kˣ) : K) • (A g).mulVec v := by
    intro g v
    rw [hA, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hWinv : IsInv (mapRep (algebraMap (D.nd.O i) K) (r x)) (LinearMap.range j) := by
    rintro g _ ⟨u, rfl⟩
    change (Rm g).mulVec (j u) ∈ LinearMap.range j
    rw [hR, ← hj]
    exact ⟨(((c g)⁻¹ : Kˣ) : K) • (mapM (toK D.nd i) M g).mulVec u, by rw [map_smul]⟩
  obtain ⟨W', hW'inv, hcompl⟩ := (hr x).2.1 (LinearMap.range j) hWinv
  have hW : ∀ g, ∀ v ∈ LinearMap.range j, (A g).mulVec v ∈ LinearMap.range j := by
    rintro g _ ⟨u, rfl⟩
    exact ⟨_, hj g u⟩
  have hW' : ∀ g, ∀ v ∈ W', (A g).mulVec v ∈ W' := by
    intro g v hv
    rw [hA, Matrix.smul_mulVec]
    exact W'.smul_mem _ (hW'inv g v hv)
  obtain ⟨Bl, hBj, hcomm⟩ := exists_left_inv A j hinj W' hcompl hW hW'

  let J : Matrix (Fin D.R.nV) (Fin k) K := LinearMap.toMatrix' j
  let B : Matrix (Fin k) (Fin D.R.nV) K := LinearMap.toMatrix' Bl
  have hJv : ∀ v, J.mulVec v = j v := fun v => LinearMap.toMatrix'_mulVec j v
  have hBv : ∀ v, B.mulVec v = Bl v := fun v => LinearMap.toMatrix'_mulVec Bl v
  have hBJ : B * J = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, hJv, hBv, hBj,
      Matrix.toLin'_one, LinearMap.id_apply]
  have hPA : ∀ g, J * B * A g = A g * (J * B) := by
    intro g
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, hJv, hBv, hcomm]
  have hJM : ∀ g, J * mapM (toK D.nd i) M g = A g * J := by
    intro g
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, hJv]
    exact hj g v
  let f := Br.toLLK (D.nbr i w hw)
  let JL : Matrix (Fin D.R.nV) (Fin k) (Br.LL D.nbr i w hw) := J.map f
  let BL : Matrix (Fin k) (Fin D.R.nV) (Br.LL D.nbr i w hw) := B.map f
  let PL : Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw) := JL * BL
  have hBJL : BL * JL = 1 := by
    change B.map f * J.map f = 1
    rw [← Matrix.map_mul, hBJ, Matrix.map_one f (map_zero f) (map_one f)]
  have hPJ : PL * JL = JL := by
    change JL * BL * JL = JL
    rw [Matrix.mul_assoc, hBJL, Matrix.mul_one]
  have hloc : ∀ g, Br.loc D.nbr i w hw (rTwO D.nd i r x) g = (A (decS D.nd w (Br.iota D.nbr i w hw g))).map f :=
    fun g => loc_eq D i w hw _ g
  have hPL : ∀ g, PL * Br.loc D.nbr i w hw (rTwO D.nd i r x) g = Br.loc D.nbr i w hw (rTwO D.nd i r x) g * PL := by
    intro g
    rw [hloc]
    have := congrArg (fun Z => Z.map f) (hPA (decS D.nd w (Br.iota D.nbr i w hw g)))
    simp only [Matrix.map_mul] at this
    exact this
  refine ⟨1, fun _ => ⟨x, hx⟩, (LinearMap.pi fun _ => Matrix.mulVecLin JL : (Fin k → Br.LL D.nbr i w hw) →ₗ[Br.LL D.nbr i w hw] (Fin 1 → Fin D.R.nV → Br.LL D.nbr i w hw)), ?_, ?_, ?_⟩
  · show Function.Injective (fun (v : Fin k → Br.LL D.nbr i w hw) (_ : Fin 1) => JL.mulVec v)
    intro v v' h
    have h1 := congrArg (fun z => BL.mulVec (z 0)) h
    change BL.mulVec (JL.mulVec v) = BL.mulVec (JL.mulVec v') at h1
    simp only [Matrix.mulVec_mulVec, hBJL, Matrix.one_mulVec] at h1
    exact h1
  · show ∀ (g : Br.G D.nbr i w hw) (v : Fin k → Br.LL D.nbr i w hw), (fun (_ : Fin 1) => JL.mulVec ((Br.loc D.nbr i w hw M g).mulVec v)) =
      fun (_ : Fin 1) => (Br.loc D.nbr i w hw (rTwO D.nd i r x) g).mulVec (JL.mulVec v)
    intro g v
    funext b
    change JL.mulVec ((Br.loc D.nbr i w hw M g).mulVec v) = (Br.loc D.nbr i w hw (rTwO D.nd i r x) g).mulVec (JL.mulVec v)
    simp only [Matrix.mulVec_mulVec]
    rw [hloc, loc_eq]
    change Matrix.mulVec (J.map f * (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).map f) v = _
    rw [← Matrix.map_mul, hJM, Matrix.map_mul]
  · refine ⟨LinearMap.ker (LinearMap.pi fun b => (Matrix.mulVecLin PL).comp (LinearMap.proj b)), ?_, ?_⟩
    · intro g u hu
      have hu' : ∀ b, PL.mulVec (u b) = 0 := fun b => congrFun (LinearMap.mem_ker.mp hu) b
      refine LinearMap.mem_ker.mpr (funext fun b => ?_)
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.mulVecLin_apply, Pi.zero_apply]
      change PL.mulVec ((Br.loc D.nbr i w hw (rTwO D.nd i r x) g).mulVec (u b)) = 0
      rw [Matrix.mulVec_mulVec, hPL, ← Matrix.mulVec_mulVec, hu', Matrix.mulVec_zero]
    · constructor
      · rw [Submodule.disjoint_def]
        rintro u ⟨(v : Fin k → Br.LL D.nbr i w hw), rfl⟩ hu
        have hu' : ∀ b, PL.mulVec (JL.mulVec v) = 0 := fun b => congrFun (LinearMap.mem_ker.mp hu) b
        funext b
        change JL.mulVec v = 0
        rw [← hPJ, ← Matrix.mulVec_mulVec]
        exact hu' b
      · rw [codisjoint_iff, eq_top_iff]
        intro u _
        refine Submodule.mem_sup.mpr ⟨fun _ => PL.mulVec (u 0), ⟨BL.mulVec (u 0), ?_⟩, fun b => u b - PL.mulVec (u 0), ?_, ?_⟩
        · funext b
          change JL.mulVec (BL.mulVec (u 0)) = (JL * BL).mulVec (u 0)
          exact Matrix.mulVec_mulVec _ _ _
        · refine LinearMap.mem_ker.mpr (funext fun b => ?_)
          simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.mulVecLin_apply, Pi.zero_apply]
          rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Subsingleton.elim b 0]
          change (JL * BL).mulVec (u 0) - (JL * BL * (JL * BL)).mulVec (u 0) = 0
          rw [Matrix.mul_assoc JL BL, ← Matrix.mul_assoc BL, hBJL, Matrix.one_mul, sub_self]
        · funext b
          change PL.mulVec (u 0) + (u b - PL.mulVec (u 0)) = u b
          exact add_sub_cancel _ _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHermNDInvTranspose
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicModulus.Row

theorem transpose_unitary {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (s : A →+* A) {J K g : Matrix n n A} (hKJ : K * J = 1)
    (hg : Formalism.UG.cT s g * J * g = J) : Formalism.UG.cT s gᵀ * Kᵀ * gᵀ = Kᵀ := by
  have hJK : J * K = 1 := mul_eq_one_comm.1 hKJ
  have h1 : (K * Formalism.UG.cT s g * J) * g = 1 := by
    rw [Matrix.mul_assoc K, Matrix.mul_assoc K, hg, hKJ]
  have h2 : g * (K * Formalism.UG.cT s g * J) = 1 := mul_eq_one_comm.1 h1
  have h3 : g * (K * Formalism.UG.cT s g) = K := by
    calc g * (K * Formalism.UG.cT s g) = g * (K * Formalism.UG.cT s g) * (J * K) := by rw [hJK, Matrix.mul_one]
      _ = g * (K * Formalism.UG.cT s g * J) * K := by simp only [Matrix.mul_assoc]
      _ = K := by rw [h2, Matrix.one_mul]
  have h4 := congrArg Matrix.transpose h3
  rw [Matrix.transpose_mul, Matrix.transpose_mul] at h4
  exact h4

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem isHermND_inv_transpose {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) : IsHermND σ (J⁻¹)ᵀ := by
  have hu : IsUnit J.det := hJ.2.isUnit
  have hm : J.map (σ : E →+* E) = Jᵀ := by
    ext i j
    exact hJ.1 j i
  have h1 : (J⁻¹).map (σ : E →+* E) * Jᵀ = 1 := by
    rw [← hm, ← Matrix.map_mul, Matrix.nonsing_inv_mul J hu]
    simp
  have h2 : (Jᵀ)⁻¹ = (J⁻¹).map (σ : E →+* E) := Matrix.inv_eq_left_inv h1
  refine ⟨fun i j => ?_, ?_⟩
  · have h3 := congrFun (congrFun h2 i) j
    rw [← Matrix.transpose_nonsing_inv] at h3
    exact h3.symm
  · rw [Matrix.det_transpose]
    exact (Matrix.isUnit_nonsing_inv_det J hu).ne_zero

def transposeGL {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (g : GL n A) : GL n A :=
  ⟨g.1ᵀ, (g⁻¹).1ᵀ, by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

theorem exists_transpose (R : Type) [CommRing R] [Algebra F R] {σ : E →ₐ[F] E} {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (g : HA R σ J) :
    ∃ g' : HA R σ (J⁻¹)ᵀ, (HA.mat R σ (J⁻¹)ᵀ g').1 = ((HA.mat R σ J g).1)ᵀ := by
  have hu : IsUnit J.det := hJ.2.isUnit
  have hKJ : JR (F := F) R J⁻¹ * JR (F := F) R J = 1 := by
    unfold JR
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul J hu]
    simp
  have hg : Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).1 * JR (F := F) R J * (HA.mat R σ J g).1 =
      JR (F := F) R J := (show HR R σ J from g).2
  exact ⟨(⟨transposeGL (HA.mat R σ J g), transpose_unitary (sigR R σ) hKJ hg⟩ : HR R σ (J⁻¹)ᵀ), rfl⟩

theorem map_vecMul_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : HA (AF F) σ J) (μ : Measure (Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure → μ.map (fun x => Matrix.vecMul x ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) = μ := by
  intro F E _ _ _ _ _ σ hσ M J hJ g μ hμ
  obtain ⟨g', hg'⟩ := exists_transpose (AF F) hJ g
  have h := PI.VolSemiDirect.W.Cj.unipotent_modulus_holds F E σ hσ M _ (isHermND_inv_transpose hJ) g' μ hμ
  have e : (fun x => Matrix.vecMul x ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) =
      fun x => ((HA.mat (AF F) σ (J⁻¹)ᵀ g').1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).mulVec x := by
    funext x
    rw [hg', Matrix.mulVec_transpose]
  rw [e]
  exact h

end GlobalTheory.AdelicModulus.Row
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerReductionH1EqStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_reduction_H1_eq : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), ∃ f : LatticeCohomology LA →ₗ[O] QuotientCohomology LA _ hI, LinearMap.ker f = (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA)) ∧ ∀ d : ↥(latticeCocycles LA), ∃ h : redT LA _ d ∈ quotientCocycles LA _ hI, f (Submodule.Quotient.mk d) = Submodule.Quotient.mk ⟨redT LA _ d, h⟩ := by
  first | exact @GlobalTheory.ReductionH1Kernel.ker_reduction_H1 | exact GlobalTheory.ReductionH1Kernel.ker_reduction_H1 | (intros; apply GlobalTheory.ReductionH1Kernel.ker_reduction_H1 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenModMonoLeft
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

theorem lenMod_mono_left : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S S' H : Submodule O M), S ≤ S' → BlochKatoDuality.lenMod S H ≤ BlochKatoDuality.lenMod S' H := by
  intro O M _ _ _ S S' H hS

  have hle : S ⊔ H ≤ S' ⊔ H := sup_le_sup_right hS H
  let f := Submodule.mapQ (H.comap (S ⊔ H).subtype) (H.comap (S' ⊔ H).subtype)
    (Submodule.inclusion hle) (fun x hx => by simpa using hx)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    simpa using hx
  exact Module.length_le_of_injective f hf

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitBreuilKisinBasisInvariantEtaleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_breuilKisin_basis_invariant_etale : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)), IsUnit T0 → (∀ n, ∃ (R : Matrix (Fin d) (Fin (tw.d' n)) (WCb l)) (R' : Matrix (Fin (tw.d' n)) (Fin d) (WCb l)), (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (R * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j)) → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g).val * T0.map (galW l (g : GQ l)) = T0) ∧ ∃ A0 A0' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, A0 i j ∈ bk.OE) ∧ (∀ i j, A0' i j ∈ bk.OE) ∧ T0.map (frobW l) = T0 * A0 ∧ A0 * A0' = 1 := by
  first | exact @GlobalTheory.LimBasis.main | exact GlobalTheory.LimBasis.main | (intros; apply GlobalTheory.LimBasis.main; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachModuleOfXPowSmulFrobeniusGammaStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_wachModule_of_X_pow_smul_frobenius_gamma : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M a : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → W.γ T m - m ∈ aN W T letπ → W.X ^ a • m ∈ W.N T → m ∈ W.N T := by
  first | exact @GlobalTheory.NL.ExtLattice.mem_N | exact GlobalTheory.NL.ExtLattice.mem_N | (intros; apply GlobalTheory.NL.ExtLattice.mem_N <;> assumption)
end

