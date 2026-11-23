module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1138
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProductOfLocalFunctionsUnitaryNeZero
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.HSupp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem toSub_cLoc_val (hE : Unr E) (w : Pl E) (x : finU (E := E) (n := n)) :
    ((toSub (UL n w) (cLoc w (x : UA E n)) : UL n w) : GLw n w) = cLoc w (x : UA E n) := by
  unfold toSub
  rw [dite_eq_left (cLoc_mem_UL E hE n w x)]

theorem factor_ne_zero (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (hK : ∀ᶠ w in cofinite, K' w = KL n w)
    (f : ∀ w : Pl E, UL n w → ℂ) (hf : ∀ᶠ w in cofinite, f w = (KL n w : Set (UL n w)).indicator 1)
    (x : finU (E := E) (n := n)) (hx : globFn S f x ≠ 0) :
    ∀ w ∈ S, f w (toSub (UL n w) (cLoc w (x : UA E n))) ≠ 0 := by
  set g : Pl E → ℂ := fun w => f w (toSub (UL n w) (cLoc w (x : UA E n))) with hg
  have hB : {w | ¬ (f w = (KL n w : Set (UL n w)).indicator 1 ∧
      toSub (UL n w) (cLoc w (x : UA E n)) ∈ KL n w)}.Finite :=
    Filter.eventually_cofinite.1 (hf.and (RegVan.eventually_toSub_mem (n := n) x))
  have hfin : (S ∩ Function.mulSupport g).Finite := by
    refine hB.subset fun w hw => ?_
    intro hc
    apply hw.2
    change f w _ = 1
    rw [hc.1]
    exact Set.indicator_of_mem hc.2 _
  intro w hwS
  by_cases hm : w ∈ Function.mulSupport g
  · have hx' : ∏ᶠ w ∈ S, g w ≠ 0 := hx
    rw [← finprod_mem_inter_mulSupport, finprod_mem_eq_finite_toFinset_prod _ hfin] at hx'
    exact Finset.prod_ne_zero_iff.1 hx' w (hfin.mem_toFinset.2 ⟨hwS, hm⟩)
  · rw [Function.notMem_mulSupport] at hm
    change g w ≠ 0
    rw [hm]
    exact one_ne_zero

end GlobalTheory.BCT.HSupp


open GlobalTheory.BCT.HSupp in
theorem GlobalTheory.BCT.finite_globFn_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ)
    (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ,
    IsTest (KL n) K' f → {q : finU (E := E) (n := n) ⧸ globLev S K' | globFn S f q.out ≠ 0}.Finite := by
  intro E _ _ _ hE n S K' hK f hf
  set F : Set (Pl E) := {w | ¬ (K' w = KL n w ∧ f w = (KL n w : Set (UL n w)).indicator 1)} with hF
  have hFfin : F.Finite := Filter.eventually_cofinite.1 (hK.2.and hf.2)
  have key := factor_ne_zero S K' hK.2 f hf.2
  have inK : ∀ x : finU (E := E) (n := n), globFn S f x ≠ 0 → ∀ w ∈ S, w ∉ F →
      toSub (UL n w) (cLoc w (x : UA E n)) ∈ K' w := by
    intro x hx w hwS hwF
    simp only [hF, Set.mem_setOf_eq, not_not] at hwF
    have h := key x hx w hwS
    rw [hwF.2] at h
    rw [hwF.1]
    by_contra hc
    exact h (Set.indicator_of_notMem hc _)
  haveI : Finite ↥(F ∩ S) := (hFfin.inter_of_left S).to_subtype
  let Φ : finU (E := E) (n := n) ⧸ globLev S K' → ∀ w : ↥(F ∩ S), UL n w.1 ⧸ K' w.1 := fun q w =>
    (toSub (UL n w.1) (cLoc w.1 (q.out : UA E n)) : UL n w.1 ⧸ K' w.1)
  refine Set.Finite.of_injOn (f := Φ)
    (t := Set.pi Set.univ fun w : ↥(F ∩ S) => {c : UL n w.1 ⧸ K' w.1 | f w.1 c.out ≠ 0}) ?_ ?_
    (Set.Finite.pi fun w => LevOpTmul.finite_supp (hK.1 w.1).1 (hf.1 w.1).1)
  · intro q hq w _
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K' w.1) (toSub (UL n w.1) (cLoc w.1 (q.out : UA E n)))
    change f w.1 (QuotientGroup.mk _ : UL n w.1 ⧸ K' w.1).out ≠ 0
    rw [hh, ((hf.1 w.1).2 h h.2 _).2]
    exact key _ hq w.1 w.2.2
  · intro q₁ hq₁ q₂ hq₂ he
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂]
    refine QuotientGroup.eq.2 ((mem_globLev_iff S K' _).2 fun w hwS => ?_)
    refine ⟨(toSub (UL n w) (cLoc w (q₁.out : UA E n)))⁻¹ * toSub (UL n w) (cLoc w (q₂.out : UA E n)), ?_, ?_⟩
    · by_cases hwF : w ∈ F
      · have := congrFun he ⟨w, hwF, hwS⟩
        exact QuotientGroup.eq.1 this
      · exact mul_mem (inv_mem (inK _ hq₁ w hwS hwF)) (inK _ hq₂ w hwS hwF)
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, toSub_cLoc_val hE, toSub_cLoc_val hE, Subgroup.coe_mul,
        Subgroup.coe_inv, map_mul, map_inv]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCmFieldEqTwoMulTotallyRealSubfieldStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_cmField_eq_two_mul_totallyRealSubfield : ∀ D : D7, Module.finrank ℚ D.host.E = Module.finrank ℚ D.host.F * 2 := by
  first | exact @GlobalTheory.cm_finrank_eq_two_mul | exact GlobalTheory.cm_finrank_eq_two_mul | (intros; apply GlobalTheory.cm_finrank_eq_two_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankGraphJetsLeChooseStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_graphJets_le_choose : ∀ {κ κ' : Type} [Field κ] [Field κ'] [Algebra ℂ κ] [Algebra ℂ κ'] (k M : ℕ) (ρ : κ →ₐ[ℂ] κ'),
  (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  letI : Algebra κ' (κ ⊗[ℂ] κ') := Algebra.TensorProduct.rightAlgebra;
  Module.finrank κ' ((κ ⊗[ℂ] κ') ⧸ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M) ≤
    (M + k - 1).choose k ∧
  Module.Finite κ' ((κ ⊗[ℂ] κ') ⧸ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M) := by
  first | exact @GlobalTheory.JetDim.jets_finrank_le | exact GlobalTheory.JetDim.jets_finrank_le | (intros; apply GlobalTheory.JetDim.jets_finrank_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorSubalgebraMvPolynomialEvalOfFlatAeval
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GraphLocal

theorem flat_polyMap_of_flat_aeval : ∀ {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ'] (A : Subalgebra ℂ K)
    (m : ℕ) (v : Fin m → A),
    (MvPolynomial.aeval v : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A).toRingHom.Flat →
    (polyMap (κ' := κ') A v).Flat := by
  intro K κ' _ _ _ _ A m v h
  have h1 : (Algebra.TensorProduct.map (AlgHom.id ℂ κ')
      (MvPolynomial.aeval v : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A)).toRingHom.Flat :=
    RingHom.Flat.tensorProductMap (f := AlgHom.id ℂ κ') (RingHom.Flat.id κ') h
  let e1 := (MvPolynomial.algebraTensorAlgEquiv (σ := Fin m) ℂ κ').symm.toRingEquiv
  let e2 := ((Algebra.TensorProduct.comm ℂ κ' A).trans (tensEquiv (κ' := κ') A)).toRingEquiv
  have h2 := ((RingHom.Flat.of_bijective (f := e1.toRingHom) e1.bijective).comp h1).comp
    (RingHom.Flat.of_bijective (f := e2.toRingHom) e2.bijective)
  convert h2 using 1
  refine MvPolynomial.ringHom_ext (fun b => Subtype.ext ?_) (fun i => Subtype.ext ?_)
  · have : (MvPolynomial.algebraTensorAlgEquiv (σ := Fin m) ℂ κ').symm (MvPolynomial.C b)
        = b ⊗ₜ 1 := by
      rw [AlgEquiv.symm_apply_eq]; simp [MvPolynomial.algebraTensorAlgEquiv_tmul, MvPolynomial.smul_eq_C_mul]
    simp [e1, e2, tensMap, this]
  · simp [e1, e2, tensMap]

end GlobalTheory.GraphLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomial
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj

namespace GlobalTheory.FockConj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem inv_neg_mat {k : Type} [Fintype k] [DecidableEq k] {R : Type} [CommRing R] (A : Matrix k k R) :
    (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · have e : ((-1 : Rˣ) • A) = -A := by simp
    rw [← e, Matrix.inv_smul' (A := A) (k := (-1 : Rˣ)) h]
    simp
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      apply h
      have : IsUnit ((-1 : R) ^ Fintype.card k) := (isUnit_neg_one (α := R)).pow _
      exact (IsUnit.mul_iff.1 hu).2
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

theorem symplOH_negSp (S T : HSp D) (x y : WO S T) :
    symplOH (negSp S) T x y = -symplOH S T x y := by
  have h : hO (negSp S) T x y = -hO S T x y := by
    unfold hO
    rw [negSp_gram, inv_neg_mat]
    simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  unfold symplOH symplO
  rw [h, mul_neg, map_neg, mul_neg]

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) (a : AF D.host.F) :
    star (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ a]
  simp [Complex.star_def]

theorem heisO_negSp_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) (S T : HSp D) (w₀ : WO S T)
    (g : WO S T → ℂ) :
    heisO ψ (negSp S) T w₀ (fun w => star (g w)) = fun w => star (heisO ψ S T w₀ g w) := by
  funext w
  unfold heisO
  rw [star_mul, symplOH_negSp, ← star_psi hψ]
  ring

theorem lineAt_neg {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (y : Matrix (Fin m) (Fin n) ℂ) :
    lineAt θ τ (-y) = -(lineAt θ τ y) := by
  have h := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ y
  refine GlobalTheory.RealLineAt.lineAt_unique D θ hθ m n τ (-y) _ _ (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ (-y)) ?_
  refine ⟨h.1.neg, fun t => ?_, fun t τ' => ?_⟩
  · have h2 := h.2.1 t
    ext i j
    have := congrFun (congrFun h2 i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at this
    simp only [Matrix.map_apply, Matrix.zero_apply, AddMonoidHom.neg_apply, Matrix.neg_apply, RingHom.map_neg, this,
      neg_zero]
  · have h3 := h.2.2 t τ'
    have e : compAt θ τ' ((-(lineAt θ τ y)) t) = -compAt θ τ' (lineAt θ τ y t) := by
      ext i j
      simp only [compAt, Matrix.map_apply, AddMonoidHom.neg_apply, Matrix.neg_apply, RingHom.map_neg]
    rw [e, h3]
    split_ifs <;> simp

end GlobalTheory.FockConj

namespace GlobalTheory.FockConj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem dRho_neg {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (τ : D.what₂.Tau) (y : Matrix (Fin m) (Fin n) ℂ) (h : Mx D m n → ℂ) :
    Formalism.IndefR.Datum.dRho hs θ τ (-y) h = -Formalism.IndefR.Datum.dRho hs θ τ y h := by
  funext x
  have e : (fun t : ℝ => hs (lineAt θ τ (-y) t) h x) = fun t => (fun s : ℝ => hs (lineAt θ τ y s) h x) (-t) := by
    funext t
    rw [lineAt_neg hθ, AddMonoidHom.neg_apply, ← map_neg]
  simp only [Formalism.IndefR.Datum.dRho, Pi.neg_apply]
  rw [e]
  exact (deriv_comp_neg (f := fun s : ℝ => hs (lineAt θ τ y s) h x) (x := 0)).trans (by rw [neg_zero])

theorem dRho_negSp_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) (θ : InfFam D) (S T : HSp D)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ (negSp S) T) θ τ z (fun w => star (g w)) = fun w => star (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g w) := by
  funext x
  simp only [Formalism.IndefR.Datum.dRho]
  have e : (fun t : ℝ => heisO ψ (negSp S) T (lineAt θ τ z t) (fun w => star (g w)) x) =
      fun t => star (heisO ψ S T (lineAt θ τ z t) g x) := by
    funext t
    rw [heisO_negSp_star hψ]
  rw [e, deriv.star]

theorem cplxO_neg {m n : ℕ} (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ)
    (z : Matrix (Fin m) (Fin n) ℂ) : cplxO (-sS) sT z = -cplxO sS sT z := by
  unfold cplxO
  rw [Matrix.mul_neg, smul_neg]

theorem aPlus_negSp_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) {θ : InfFam D} (hθ : IsInfFam θ)
    (S T : HSp D) (τ : D.what₂.Tau) (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    aPlus (heisO ψ (negSp S) T) θ τ (cplxO (-sS) sT) u (fun w => star (g w)) =
      fun w => star (aPlus (heisO ψ S T) θ τ (cplxO sS sT) u g w) := by
  funext w
  simp only [aPlus, crea, cplxO_neg, dRho_neg hθ, dRho_negSp_star hψ]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    smul_eq_mul, star_mul, star_sub, Complex.star_def, Complex.conj_I, map_inv₀, Complex.conj_ofReal]
  ring

theorem foldr_negSp_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) {θ : InfFam D} (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (L : List (FVar D T.rank S.rank)) (g : WO S T → ℂ) :
    L.foldr (fun i h => aPlusAll (heisO ψ (negSp S) T) θ (fun τ => cplxO (-sS τ) (sT τ)) BS BT i h)
        (fun w => star (g w)) =
      fun w => star (L.foldr (fun i h => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i h) g w) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.foldr_cons, List.foldr_cons, ih]
    exact aPlus_negSp_star hψ hθ S T a.1 (sS a.1) (sT a.1) _ _

end GlobalTheory.FockConj

namespace GlobalTheory.FockConj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pureTensorO_negSp_monomial : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO (negSp S) T → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (k : FVar D T.rank S.rank →₀ ℕ) (x : WO S T), pureTensorO ψ θ (negSp S) T (fun τ => -sS τ) sT BS BT f (MvPolynomial.monomial k 1) x = starRingEnd ℂ (pureTensorO ψ θ S T sS sT BS BT (fun w => starRingEnd ℂ (f w)) (MvPolynomial.monomial k 1) x) := by
  intro D ψ θ S T sS sT BS BT f hψ hθ k x
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  have h1 : pureTensorO ψ θ (negSp S) T (fun τ => -sS τ) sT BS BT f (MvPolynomial.monomial k 1) =
      opPow (aPlusAll (heisO ψ (negSp S) T) θ (fun τ => cplxO (-sS τ) (sT τ)) BS BT) k f := by
    have := (MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ).constr_basis ℂ
      (fun k => opPow (aPlusAll (heisO ψ (negSp S) T) θ (fun τ => cplxO (-sS τ) (sT τ)) BS BT) k f) k
    rwa [MvPolynomial.coe_basisMonomials] at this
  have h2 : pureTensorO ψ θ S T sS sT BS BT (fun w => starRingEnd ℂ (f w)) (MvPolynomial.monomial k 1) =
      opPow (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) k (fun w => starRingEnd ℂ (f w)) := by
    have := (MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ).constr_basis ℂ
      (fun k => opPow (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) k
        (fun w => starRingEnd ℂ (f w))) k
    rwa [MvPolynomial.coe_basisMonomials] at this
  rw [h1, h2, opPow, opPow]
  have hf : f = fun w => star (starRingEnd ℂ (f w)) := by
    funext w
    simp
  conv_lhs => rw [hf]
  rw [foldr_negSp_star hn hθ S T sS sT BS BT]
  rfl

end GlobalTheory.FockConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdKaehlerWedgeUniformiserResidueIndependent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem formOrd_dForm_cons_of_ord_eq_one : ∀ {K : Type} [Field K] (cK : ℂ →+* K) (F : Place cK) (m : ℕ) (π : K) (y : Fin m → K),
  F.ord π = 1 → (∀ i, y i ∈ F.ring) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK y P ≠ 0 ∧ (MvPolynomial.eval₂ cK y P)⁻¹ ∈ F.ring) →
  TrBasis cK (Fin.cons π y : Fin (m + 1) → K) →
  (fun ω => @dite ℤ (∃ a, F.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cK (Fin.cons π y : Fin (m + 1) → K)) = 0 := by
  intro K _ cK F m π y hπ hy hP hB
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp [Place.ord] at hπ
  have hπm : π ∈ F.ring := (F.ord_nonneg_iff hπ0).1 (by rw [hπ]; norm_num)
  have hirr : Irreducible (⟨π, hπm⟩ : F.ring) := by
    obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible F.ring
    have hne : (⟨π, hπm⟩ : F.ring) ≠ 0 := fun h => hπ0 (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne ht
    have e : π = ((u : F.ring) : K) * (t : K) ^ n := by
      simpa using congrArg Subtype.val hu
    have hu0 : ((u : F.ring) : K) ≠ 0 := (u.isUnit.map F.ring.subtype).ne_zero
    have ht0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
    have h1 : F.ord π = n := by
      rw [e, F.ord_mul hu0 (pow_ne_zero _ ht0), F.ord_eq_zero u.isUnit, F.ord_pow,
        F.ord_irreducible ht]
      simp
    obtain rfl : n = 1 := by
      rw [hπ] at h1
      exact_mod_cast h1.symm
    rw [hu, pow_one]
    exact (irreducible_units_mul u).2 ht
  refine formOrd_dForm_uniformiser_cons cK m F ⟨π, hπm⟩ (fun i => ⟨y i, hy i⟩) hirr ?_ ⟨_, hB⟩
  intro P hP0
  obtain ⟨h0, hi⟩ := hP P hP0
  have e : ((MvPolynomial.eval₂ F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P : F.ring) : K) =
      MvPolynomial.eval₂ cK y P :=
    MvPolynomial.eval₂_comp_left F.ring.subtype F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P
  refine IsUnit.of_mul_eq_one (⟨_, hi⟩ : F.ring) (Subtype.ext ?_)
  change ((MvPolynomial.eval₂ F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P : F.ring) : K) * _ = 1
  rw [e]
  exact mul_inv_cancel₀ h0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMemberSectionNeZeroIsPrimeAffineChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.GenericMember
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct

namespace GlobalTheory.GenericMember

theorem genSec_chart_ne_zero_and_isPrime : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X) (L : LB X) (hL : L.IsLB) (b : Fin N → L.Sec) (V : X.Opens) (hne : (V : Set X).Nonempty) (hW : IsAffineOpen (π ⁻¹ᵁ V)) (c : L.ι) (hVc : V ≤ L.U c) (j : Fin N), IsUnit (resG X hVc ((b j).f c)) → letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra; ∀ e : FractionRing (MvPolynomial (Fin N) k) ⊗[k] Γ(X, V) ≃+* Γ(X', π ⁻¹ᵁ V), (∀ a, e (1 ⊗ₜ a) = (π.app V).hom a) → (∀ q, e (q ⊗ₜ 1) = ((Scheme.ΓSpecIso _).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom q) → (genSec k N f' π L b).f (fun _ => c) ≠ 0 ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩ = ⊤ ∨ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).IsPrime ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).comap (π.app V).hom = ⊥) := by
  intro k _ N X X' _ f f' π L hL b V hne hW c hVc j hj
  letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra
  intro e he1 he2
  haveI : Nonempty V := hne.to_subtype
  set a : Fin N → Γ(X, V) := fun i => resG X hVc ((b i).f c) with ha
  set t₀ : FractionRing (MvPolynomial (Fin N) k) ⊗[k] Γ(X, V) :=
    ∑ i, algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i) ⊗ₜ[k] a i with ht
  obtain ⟨ht0, hI⟩ := GlobalTheory.GenericForm.span_genericForm_isPrime_or_eq_top k Γ(X, V) N a j hj t₀ rfl
  have hWU : π ⁻¹ᵁ V ≤ (L.pull π).U (fun _ => c) := fun x hx => Set.mem_iInter.2 fun _ => hVc hx
  have hsum : ∀ J, (genSec k N f' π L b).f J =
      ∑ i, resG X' le_top (genVar k N f' i) * (secPull (b i) π).f J := by
    intro J
    let F : (L.pull π).Sec →+ Γ(X', (L.pull π).U J) :=
      { toFun := fun s => s.f J, map_zero' := rfl, map_add' := fun _ _ => rfl }
    show F (∑ i, genVar k N f' i • secPull (b i) π) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    rfl
  have key : resG X' hWU ((genSec k N f' π L b).f (fun _ => c)) = e t₀ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum (fun _ => c), map_sum, ht, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    have hq : algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i) ⊗ₜ[k] a i =
        (algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i) ⊗ₜ[k] (1 : Γ(X, V))) *
          ((1 : FractionRing (MvPolynomial (Fin N) k)) ⊗ₜ[k] a i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hq, map_mul, he1, he2]
    congr 1
    · have e2 : f'.appTop ≫ X'.presheaf.map (homOfLE (le_top : (L.pull π).U (fun _ => c) ≤ ⊤)).op ≫
          X'.presheaf.map (homOfLE hWU).op = f'.appLE ⊤ (π ⁻¹ᵁ V) le_top := by
        simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, ← Functor.map_comp]
        rfl
      exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing (MvPolynomial (Fin N) k)))).inv.hom
        (algebraMap (MvPolynomial (Fin N) k) (FractionRing (MvPolynomial (Fin N) k)) (MvPolynomial.X i)))) e2
    · have e1 : π.appLE (L.U c) ((L.pull π).U (fun _ => c)) ((GlobalTheory.chartPullPull L π).le (fun _ => c)) ≫
          X'.presheaf.map (homOfLE hWU).op = X.presheaf.map (homOfLE hVc).op ≫ π.app V := by
        rw [Scheme.Hom.naturality]
        simp only [Scheme.Hom.appLE, Category.assoc, ← Functor.map_comp]
        rfl
      exact congrArg (fun φ => φ.hom ((b i).f c)) e1
  have hid : (secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩ =
      Ideal.span {e t₀} := by
    rw [ideal_secIdeal (LB.isLB_pull hL π) _ ⟨π ⁻¹ᵁ V, hW⟩ (fun _ => c) hWU]
    exact congrArg (fun x => Ideal.span {x}) key
  have hmap : Ideal.span {e t₀} = Ideal.map e (Ideal.span {t₀}) := by
    rw [Ideal.map_span, Set.image_singleton]
  refine ⟨fun h0 => ht0 (e.injective ?_), ?_⟩
  · rw [map_zero, ← key, h0, map_zero]
  · rw [hid]
    rcases hI with h | ⟨hp, hx⟩
    · left
      rw [hmap, h, Ideal.map_top]
    · right
      refine ⟨?_, ?_⟩
      · haveI := hp
        rw [hmap]
        exact Ideal.map_isPrime_of_equiv e
      · rw [eq_bot_iff]
        intro x hx'
        rw [Ideal.mem_bot]
        apply hx x
        rw [Ideal.mem_comap, ← he1, Ideal.mem_span_singleton'] at hx'
        obtain ⟨d, hd⟩ := hx'
        rw [Ideal.mem_span_singleton']
        refine ⟨e.symm d, e.injective ?_⟩
        rw [map_mul, RingEquiv.apply_symm_apply, hd]

end GlobalTheory.GenericMember
end

