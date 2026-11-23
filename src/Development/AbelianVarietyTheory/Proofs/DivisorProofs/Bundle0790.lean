module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import GroundTheory.GlobalFields.Adele.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0651
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0041
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0208
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
public import Formalism.PolynomialDimension.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0780
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLocAdele
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.PlaceApprox

variable {F : Type} [Field F] [NumberField F]


open Classical in
def locAdele (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F)))
    (p : ((v : S₂) → Fv F v.1) × ((w : S₁) → w.1.Completion)) : AF F :=
  ((fun u : InfinitePlace F => if h : u ∈ S₁ then p.2 ⟨u, h⟩ else 0 : InfiniteAdeleRing F),
    ∑ v : S₂, GlobalTheory.AdelicU.singleFin v.1 (p.1 v))

open Classical in
theorem continuous_locAdele (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (locAdele S₁ S₂) := by
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun u => ?_
    by_cases h : u ∈ S₁
    · simp only [h, dite_true]
      exact (continuous_apply _).comp continuous_snd
    · simp only [h, dite_false]
      exact continuous_const
  · exact continuous_finsetSum _ fun v _ =>
      (GlobalTheory.AdelicU.continuous_singleFin v.1).comp ((continuous_apply v).comp continuous_fst)

open Classical in
theorem locAdele_zero (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) :
    locAdele S₁ S₂ 0 = 0 := by
  refine Prod.ext ?_ ?_
  · funext u
    change (if h : u ∈ S₁ then (0 : u.Completion) else 0) = 0
    split_ifs <;> rfl
  · simp [locAdele]

open Classical in
theorem mul_eq_locAdele {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F}
    (hε : IsPlacesIdem S₁ S₂ ε) (a : AF F) :
    ε * a = locAdele S₁ S₂ ((fun v => evalV F v.1 (sndA F a)), (fun w => fstA F a w.1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hε
  refine Prod.ext ?_ ?_
  · funext u
    change fstA F ε u * fstA F a u = _
    by_cases h : u ∈ S₁
    · simp only [locAdele, h, dite_true, h1 u h, one_mul]
    · simp only [locAdele, h, dite_false, h2 u h, zero_mul]
  · apply GlobalTheory.AdelicU.af_ext
    intro u
    change evalV F u (sndA F ε) * evalV F u (sndA F a) = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [locAdele, map_sum]
    by_cases h : u ∈ S₂
    · rw [h3 u h, one_mul, Finset.sum_eq_single ⟨u, h⟩]
      · exact (GlobalTheory.AdelicU.evalV_singleFin_self u _).symm
      · intro b _ hb
        exact GlobalTheory.AdelicU.evalV_singleFin_ne (fun e => hb (Subtype.ext e.symm)) _
      · intro hn; exact absurd (Finset.mem_univ _) hn
    · rw [h4 u h, zero_mul, Finset.sum_eq_zero]
      intro b _
      exact GlobalTheory.AdelicU.evalV_singleFin_ne (fun e => h (by rw [e]; exact b.2)) _

theorem loc_sub_algebraMap (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (x : AF F) (t : F) :
    (((fun v : S₂ => evalV F v.1 (sndA F (x - algebraMap F (AF F) t))),
      (fun w : S₁ => fstA F (x - algebraMap F (AF F) t) w.1)) :
        ((v : S₂) → Fv F v.1) × ((w : S₁) → w.1.Completion)) =
      ((fun v : S₂ => evalV F v.1 (sndA F x)), (fun w : S₁ => fstA F x w.1)) -
        ((fun v : S₂ => algebraMap F (v.1.adicCompletion F) t), (fun w : S₁ => algebraMap F w.1.Completion t)) := by
  refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
  · simp only [map_sub, AlgHom.commutes, Prod.fst_sub, Pi.sub_apply]
  · simp only [map_sub, AlgHom.commutes, Prod.snd_sub, Pi.sub_apply]
    rfl

theorem weak_approx_idem : ∀ (F : Type) [Field F] [NumberField F], ∀ (S₁ : Finset (InfinitePlace F))
    (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε →
    ∀ (x : AF F) (U : Set (AF F)), U ∈ 𝓝 (0 : AF F) → ∃ t : F, ε * (x - algebraMap F (AF F) t) ∈ U := by
  intro F _ _ S₁ S₂ ε hε x U hU
  set c : ((v : S₂) → Fv F v.1) × ((w : S₁) → w.1.Completion) :=
    ((fun v : S₂ => evalV F v.1 (sndA F x)), (fun w : S₁ => fstA F x w.1)) with hc
  have hO : {p | locAdele S₁ S₂ (c - p) ∈ U} ∈ 𝓝 c := by
    have hcont : Continuous fun p => locAdele S₁ S₂ (c - p) :=
      (continuous_locAdele S₁ S₂).comp (continuous_const.sub continuous_id)
    have h0 : locAdele S₁ S₂ (c - c) = 0 := by
      rw [sub_self, locAdele_zero]
    exact hcont.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)
  have hd := GroundTheory.Global.denseRange_algebraMap_prod_pi (K := F) S₂ S₁
  obtain ⟨_, hy, t, rfl⟩ := mem_closure_iff_nhds.1 (hd c) _ hO
  refine ⟨t, ?_⟩
  rw [mul_eq_locAdele hε, loc_sub_algebraMap]
  exact hy

end GlobalTheory.PlaceApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalPullbackPowerIsRigidifiedRelAmple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin.DiagPow

theorem eSec_diag {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    eSec A ≫ (lift (𝟙 A) (𝟙 A)).left = eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
  unfold eSec
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  rw [comp_lift, comp_lift]
  congr 1
  rw [Hom.one_def, ← Category.assoc, Category.comp_id, toUnit_unique (η[A] ≫ toUnit A) (𝟙 _), Category.id_comp]

theorem diagPow_isLB_rigidified_relAmple : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (d : ℕ), 0 < d →
      (diagPow A Q d).IsLB ∧ Out.Rigidified A (diagPow A Q d) ∧ Out.RelAmple A (diagPow A Q d) := by
  intro S A _ _ Q hQ d hd
  obtain ⟨hA, hQL, ⟨t₁, ht₁⟩, -, -, hamp⟩ := hQ
  have hM : (Q.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hQL _
  have hD : (diagPow A Q d).IsLB := LB.isLB_linComb hQL _ _
  have hcls : CechPic.cls _ hD = d • CechPic.cls _ hM := by
    refine (CechPic.cls_linComb hQL (K := Fin 1) (fun _ => (lift (𝟙 A) (𝟙 A)).left) (fun _ => (d : ℤ)) hD).trans ?_
    rw [Fintype.sum_unique, CechPic.cls_pull hQL _ hM]
    exact natCast_zsmul _ d
  refine ⟨hD, ?_, GlobalTheory.SiegelOfTheta.relAmple_of_pow hA hM hD hd hcls hamp⟩
  have h₁ : CechPic.cls _ (pull_isLB hQL (lift (1 : A ⟶ A) (𝟙 A)).left) = 0 :=
    (CechPic.cls_eq_zero_iff _).2 ⟨t₁, ht₁⟩
  refine (CechPic.cls_eq_zero_iff (pull_isLB hD (eSec A))).1 ?_
  rw [CechPic.cls_pull hD, hcls, map_nsmul, CechPic.cls_pull hQL, ← CechPic.pull_comp, eSec_diag,
    CechPic.pull_comp, ← CechPic.cls_pull hQL _ (pull_isLB hQL _), h₁, map_zero, nsmul_zero]

end GlobalTheory.ActFin.DiagPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLastZeroInclusion
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare


open GlobalTheory.Branching.AddColumn in
theorem exists_eq_incl_of_last_eq_zero : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin (n + 1) → ℕ), ν (Fin.last n) = 0 → ∀ x ∈ dualWeyl K (n + 1) (n + 1) ν, ∃ x' ∈ dualWeyl K (n + 1) n (fun i => ν i.castSucc), x = incl K n x' := by
  intro K _ _ n ν hν x hx
  have hinj : Function.Injective
      (Prod.map id Fin.castSucc : Fin (n + 1) × Fin n → Fin (n + 1) × Fin (n + 1)) :=
    Function.injective_id.prodMap (Fin.castSucc_injective n)
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hx ⊢
  obtain ⟨x', rfl⟩ := exists_rename_eq_of_vars_subset_range x _ hinj (by
    rintro ⟨a, s⟩ hv
    induction s using Fin.lastCases with
    | cast s => exact ⟨(a, s), rfl⟩
    | last =>
      exfalso
      obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support _).1 (Finset.mem_coe.1 hv)
      have h := congrFun (hx.1 (mem_support_iff.1 hd)) (Fin.last n)
      rw [hν, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_eq_zero_iff] at h
      have h2 := h _ hvd
      simp [colW] at h2
      exact Finsupp.mem_support_iff.1 hvd h2)
  refine ⟨x', ⟨fun u hu => ?_, fun l j hlj => ?_⟩, rfl⟩
  · rw [← coeff_rename_mapDomain _ hinj] at hu
    funext i
    rw [← (weight_mapDomain (n + 1) n u).1, hx.1 hu]
  · have h := hx.2 l.castSucc j.castSucc (Fin.castSucc_lt_castSucc_iff.2 hlj)
    rw [colAddGen_rename_castSucc] at h
    apply rename_injective _ (Option.map_injective hinj)
    rw [h, rename_rename, rename_rename]
    rfl

end GlobalTheory.BrCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLeOfHighestVectorRowOperatorStable
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare

theorem rowDiv_succ_rec (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) (k : ℕ) :
    ((k : MvPolynomial (Fin r × Fin m) R) + 1) * rowDiv R a b (k + 1) f +
      (if a = b then 1 else 0) * (k : MvPolynomial (Fin r × Fin m) R) * rowDiv R a b k f =
      rowE R r m a b (rowDiv R a b k f) := by
  unfold rowDiv
  induction f using MvPolynomial.induction_on generalizing k with
  | C c =>
    have h : rowGen R a b (C c : MvPolynomial (Fin r × Fin m) R) = Polynomial.C (C c) := by
      simp [rowGen]
    rw [h]
    cases k with
    | zero => simp [rowE_C, Polynomial.coeff_C]
    | succ k => simp
  | add p q hp hq =>
    simp only [map_add (f := _), Polynomial.coeff_add, ← hp, ← hq]
    ring
  | mul_X p v hp =>
    obtain ⟨c, s⟩ := v
    set y : MvPolynomial (Fin r × Fin m) R := if b = c then X (a, s) else 0 with hy
    have hX : rowGen R a b (X (c, s) : MvPolynomial (Fin r × Fin m) R) =
        Polynomial.C (X (c, s)) + Polynomial.C y * Polynomial.X := by
      rw [rowGen, aeval_X, hy]
      by_cases h : b = c
      · rw [if_pos h, if_pos h.symm, mul_comm]
      · rw [if_neg h, if_neg (Ne.symm h), map_zero, zero_mul]
    have hx : rowE R r m a b (X (c, s)) = y := rowE_X R r m a b c s
    have hy' : rowE R r m a b y = (if a = b then 1 else 0) * y := by
      rw [hy]
      split_ifs with h1 h2 h2
      · rw [rowE_X, if_pos h2.symm, one_mul]
      · rw [rowE_X, if_neg (Ne.symm h2), zero_mul]
      · simp
      · simp
    have hs : ∀ j, (rowGen R a b (p * X (c, s))).coeff (j + 1) =
        (rowGen R a b p).coeff (j + 1) * X (c, s) + (rowGen R a b p).coeff j * y := by
      intro j
      rw [map_mul, hX, mul_add, ← mul_assoc, Polynomial.coeff_add, Polynomial.coeff_mul_X, Polynomial.coeff_mul_C,
        Polynomial.coeff_mul_C]
    have h0 : (rowGen R a b (p * X (c, s))).coeff 0 = (rowGen R a b p).coeff 0 * X (c, s) := by
      rw [map_mul, hX, mul_add, ← mul_assoc, Polynomial.coeff_add, Polynomial.coeff_mul_X_zero, Polynomial.coeff_mul_C,
        add_zero]
    cases k with
    | zero =>
      rw [hs, h0, rowE_mul, hx, ← hp]
      push_cast
      ring
    | succ k =>
      rw [hs (k + 1), hs k, map_add (f := rowE R r m a b), rowE_mul, rowE_mul, hx, hy', ← hp, ← hp]
      push_cast
      ring

theorem rowDiv_mem_of_rowE {K : Type} [Field K] [CharZero K] {r m : ℕ} (a b : Fin r)
    (M : Submodule K (MvPolynomial (Fin r × Fin m) K)) (h : ∀ f ∈ M, rowE K r m a b f ∈ M) (k : ℕ)
    {f : MvPolynomial (Fin r × Fin m) K} (hf : f ∈ M) : rowDiv K a b k f ∈ M := by
  induction k with
  | zero => rw [(rowE_eq_rowDiv K r m a b f).2]; exact hf
  | succ k ih =>
    have hrec := rowDiv_succ_rec K a b f k
    have h1 : (if a = b then 1 else 0) * (k : MvPolynomial (Fin r × Fin m) K) * rowDiv K a b k f ∈ M := by
      split_ifs
      · rw [one_mul, ← nsmul_eq_mul]; exact nsmul_mem ih k
      · simp
    have h2 : ((k + 1 : ℕ) : K) • rowDiv K a b (k + 1) f ∈ M := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Nat.cast_succ, eq_sub_of_add_eq hrec]
      exact M.sub_mem (h _ ih) h1
    exact (M.smul_mem_iff (Nat.cast_ne_zero.2 k.succ_ne_zero)).1 h2

theorem dualWeyl_le_of_rowE_stable : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin n → ℕ), Antitone ν →
    ∀ M : Submodule K (MvPolynomial (Fin n × Fin n) K), hw K le_rfl ν ∈ M →
      (∀ a b : Fin n, ∀ f ∈ M, rowE K n n a b f ∈ M) → dualWeyl K n n ν ≤ M := by
  intro K _ _ n ν hν M h0 hE
  rw [Formalism.L2.Col.dualWeyl_eq_weyl K le_rfl ν hν, weyl, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact h0
  | cons x w ih => exact rowDiv_mem_of_rowE x.1 x.2.1 M (hE _ _) x.2.2 ih

end GlobalTheory.BrCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylOrthonormalBasisValuesAtUnitarySumSqLeOn
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.DualWeyl.EvBound

theorem sum_sq_norm_evalAt_onBasis_eq_one (n : ℕ) (la : Fin n → ℕ) (hla : Antitone la) (g : UN n) :
    ∑ i, ‖evalAt g.1 (((toSpace la).symm (onBasis la i) : nabla la ℂ) : Pol n ℂ)‖ ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := GlobalTheory.DualWeyl.Repro.exists_repr la
  have h1 := GlobalTheory.DualWeyl.Repro.normSq_repr hla hk
  let e : Idx la → nabla la ℂ := fun i => (toSpace la).symm (onBasis la i)
  have he : ∀ i, toSpace la (e i) = onBasis la i := fun i => (toSpace la).apply_symm_apply _
  let u : UN n := ⟨g.1ᵀ, transpose_mem_unitaryGroup g.2⟩
  rw [← h1, ← normSq_rhoU u⁻¹, ← norm_toSpace_sq, ← (onBasis la).sum_sq_norm_inner_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← he, inner_toSpace, GlobalTheory.DualWeyl.Repro.form_rhoU_repr hk]
  rfl

theorem sum_sq_norm_evalAt_onBasis_le_one : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → ∀ u : UN n,
    ∑ i, ‖evalAt u.1 (((toSpace la).symm (onBasis la i) : nabla la ℂ) : Pol n ℂ)‖ ^ 2 ≤ 1 :=
  fun n la hla u => (sum_sq_norm_evalAt_onBasis_eq_one n la hla u).le

end GlobalTheory.DualWeyl.EvBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorEvaluationTranslateKronecker
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section
namespace GlobalTheory.DefPt

theorem evalAt_mul_intVec {n : ℕ} (la : Fin n → ℕ) {K S : Type} [Field K] [CharZero K] [CommRing S] (φ : K →+* S)
    (g : Matrix (Fin n) (Fin n) K) (y : Matrix (Fin n) (Fin n) S) (j : Idx la) :
    GlobalTheory.DualWeyl.evalAt (g.map φ * y) (map (Int.castRingHom S) (intVec la j)) =
      ∑ i, φ (rhoMat la g i j) * GlobalTheory.DualWeyl.evalAt y (map (Int.castRingHom S) (intVec la i)) := by
  have h1 : (rho la K gᵀ (basis la K j) : Pol n K) = ∑ i, rhoMat la g i j • (basis la K i : Pol n K) := by
    have h := (basis la K).sum_repr (rho la K gᵀ (basis la K j))
    conv_lhs => rw [← h]
    simp only [Submodule.coe_sum, Submodule.coe_smul, rhoMat, LinearMap.toMatrix_apply]
  have hmap : ∀ i, map φ (basis la K i : Pol n K) = map (Int.castRingHom S) (intVec la i) := by
    intro i
    rw [coe_basis, map_map, RingHom.ext_int (φ.comp (Int.castRingHom K)) (Int.castRingHom S)]
  rw [coe_rho, Matrix.transpose_transpose] at h1
  rw [← hmap j, ← evalAt_rowAct, ← GlobalTheory.NabStab.map_rowAct, coe_basis, ← coe_basis, h1]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_C_mul, map_mul, map_C]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmap i]
  simp [GlobalTheory.DualWeyl.evalAt]

theorem tval_translate : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ) (K S : Type) [Field K] [CharZero K] [CommRing S] (φ : K →+* S) (x : TIdx la → K) (g : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S), tval la (fun I => φ (x I)) (fun t => (g t).map φ * y t) = tval la (fun I => φ (((kron fun t => rhoMat (la t) (g t)) *ᵥ x) I)) y := by
  intro T _ _ N la K S _ _ _ φ x g y
  unfold tval
  simp only [evalAt_mul_intVec, Finset.prod_univ_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, kron, Matrix.of_apply, map_sum, map_mul, map_prod, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

end GlobalTheory.DefPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTvalInvertible
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.CoordVanish

theorem coeff_eq_zero_of_evalAt {n : ℕ} (la : Fin n → ℕ) (K : Type) [Field K] [CharZero K] (c : Idx la → K)
    (h : ∀ y : Matrix (Fin n) (Fin n) K, y.det ≠ 0 →
      ∑ i, c i * DualWeyl.evalAt y (map (Int.castRingHom K) (intVec la i)) = 0) : c = 0 := by
  classical
  set Q : Pol n K := ∑ i, c i • map (Int.castRingHom K) (intVec la i) with hQ
  have hQe : ∀ y : Matrix (Fin n) (Fin n) K,
      DualWeyl.evalAt y Q = ∑ i, c i * DualWeyl.evalAt y (map (Int.castRingHom K) (intVec la i)) := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hQ, map_sum, smul_eq_mul]
  set D : Pol n K := (Matrix.of fun a b : Fin n => (X (a, b) : Pol n K)).det with hD
  have hDe : ∀ y : Matrix (Fin n) (Fin n) K, DualWeyl.evalAt y D = y.det := by
    intro y
    rw [hD, AlgHom.map_det]
    congr 1
    ext a b
    simp
  have hev : ∀ (v : Fin n × Fin n → K) (p : Pol n K),
      eval v p = DualWeyl.evalAt (Matrix.of fun a b => v (a, b)) p := by
    intro v p
    simp [DualWeyl.evalAt, aeval_eq_eval]
  have hQD : Q * D = 0 := by
    refine MvPolynomial.funext fun v => ?_
    rw [hev, map_mul, hDe, map_zero]
    by_cases hd : (Matrix.of fun a b => v (a, b)).det = 0
    · rw [hd, mul_zero]
    · rw [hQe, h _ hd, zero_mul]
  have hD0 : D ≠ 0 := by
    intro h0
    have := hDe 1
    rw [h0, map_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hQ0 : Q = 0 := (mul_eq_zero.mp hQD).resolve_right hD0
  funext i
  exact Fintype.linearIndependent_iff.mp (intVec_spec la K).1 c hQ0 i

theorem eq_zero_of_prod {T : Type} [Fintype T] [DecidableEq T] {ι : T → Type} [∀ t, Fintype (ι t)]
    {A : T → Type} {K : Type} [Field K] (g : ∀ t, ι t → A t → K) (a0 : ∀ t, A t)
    (H : ∀ t (c : ι t → K), (∀ b : A t, ∑ i, c i * g t i b = 0) → c = 0)
    (x : (∀ t, ι t) → K) (hx : ∀ a : ∀ t, A t, ∑ I, x I * ∏ t, g t (I t) (a t) = 0) : x = 0 := by
  classical
  have key : ∀ S : Finset T, ∀ x : (∀ t, ι t) → K,
      (∀ a : ∀ t, A t, ∑ I, x I * ∏ t ∈ S, g t (I t) (a t) = 0) →
      ∀ I : ∀ t, ι t, ∑ I' ∈ Finset.univ.filter (fun I' : ∀ t, ι t => ∀ t ∈ S, I' t = I t), x I' = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro x hx I
      simpa using hx a0
    | insert s S hs IH =>
      intro x hx I
      have step : ∀ i : ι s, ∀ a : ∀ t, A t,
          ∑ I', (if I' s = i then x I' else 0) * ∏ t ∈ S, g t (I' t) (a t) = 0 := by
        intro i a
        have hc := H s (fun i => ∑ I', (if I' s = i then x I' else 0) * ∏ t ∈ S, g t (I' t) (a t)) (fun b => by
          have h1 := hx (Function.update a s b)
          have h2 : ∀ I' : ∀ t, ι t, ∏ t ∈ S, g t (I' t) (Function.update a s b t) = ∏ t ∈ S, g t (I' t) (a t) := by
            intro I'
            refine Finset.prod_congr rfl fun t ht => ?_
            have : t ≠ s := fun h => hs (h ▸ ht)
            rw [Function.update_of_ne this]
          simp only [Finset.prod_insert hs, Function.update_self, h2] at h1
          refine Eq.trans ?_ h1
          simp only [Finset.sum_mul, ite_mul, zero_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun I' _ => ?_
          rw [Finset.sum_ite_eq]
          simp only [Finset.mem_univ, if_true]
          ring)
        exact congrFun hc i
      have h3 := IH _ (step (I s)) I
      rw [Finset.sum_filter] at h3
      rw [Finset.sum_filter]
      refine Eq.trans (Finset.sum_congr rfl fun I' _ => ?_) h3
      simp only [Finset.forall_mem_insert]
      by_cases h4 : I' s = I s <;> by_cases h5 : ∀ t ∈ S, I' t = I t <;> simp [h4, h5]
  funext I
  have h := key Finset.univ x (by simpa using hx) I
  have h6 : Finset.univ.filter (fun I' : ∀ t, ι t => ∀ t ∈ (Finset.univ : Finset T), I' t = I t) = {I} := by
    ext I'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, forall_const]
    exact ⟨fun h => funext h, fun h t => h ▸ rfl⟩
  rw [h6, Finset.sum_singleton] at h
  exact h

theorem eq_zero_of_tval_invertible : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ)
    (K : Type) [Field K] [CharZero K] (x : TIdx la → K),
    (∀ y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K, (∀ t, (y t).det ≠ 0) → tval la x y = 0) → x = 0 := by
  intro T _ _ N la K _ _ x hx
  exact eq_zero_of_prod (ι := fun t => Idx (la t))
    (A := fun t => {M : Matrix (Fin (N t)) (Fin (N t)) K // M.det ≠ 0})
    (fun t i M => DualWeyl.evalAt M.1 (map (Int.castRingHom K) (intVec (la t) i))) (fun t => ⟨1, by simp⟩)
    (fun t c hc => coeff_eq_zero_of_evalAt (la t) K c fun y hy => hc ⟨y, hy⟩) x
    (fun a => hx (fun t => (a t).1) fun t => (a t).2)

end GlobalTheory.CoordVanish
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceOfStrictlyHenselianStaStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_cohomology_equivalence_of_strictly_henselian_stalks : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E E' : Spc) (α : E ⟶ E') (p : E' ⟶ sch.obj S), Finitary F → QcqsOver (α ≫ p) → QcqsOver p → (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R ((bcMap α p).app (Over.mk s)) F) → ∀ (U : Over S), Etale U.hom → ∀ n : ℤ, (∀ x : H R ((bc (α ≫ p)).obj U) F n, ∃ (V : Over S) (h : V ⟶ U) (y : H R ((bc p).obj V) F n), Etale V.hom ∧ Surjective h.left ∧ pull R ((bcMap α p).app V) F n y = pull R ((bc (α ≫ p)).map h) F n x) ∧ ∀ y : H R ((bc p).obj U) F n, pull R ((bcMap α p).app U) F n y = 0 → ∃ (V : Over S) (h : V ⟶ U), Etale V.hom ∧ Surjective h.left ∧ pull R ((bc p).map h) F n y = 0 := by
  first
  | exact @GlobalTheory.EtC.loc_glob_classes
  | exact GlobalTheory.EtC.loc_glob_classes
  | (intros; apply GlobalTheory.EtC.loc_glob_classes <;> assumption)
end

