module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePolynomialsOfCarriedEigensystem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.CarriedHecke

theorem exists_sys_of_mem_span {K V H I J : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup H] [Module ℂ H]
    (σ : K →+* ℂ) (op : I → Module.End K V) (j : V →ₛₗ[σ] H) (h : J → Module.End ℂ H) (ι : J → I)
    (hj : ∀ i f, j (op (ι i) f) = h i (j f)) (hc : Formalism.L2.Col.PairComm h) (C : (I → K) → Prop) (v : H)
    (hv : v ∈ Submodule.span ℂ (j '' (Formalism.L2.Col.eigSum op C : Set V))) (hv0 : v ≠ 0) (l : J → ℂ)
    (he : ∀ i, h i v = l i • v) : ∃ x, C x ∧ ∀ i, σ (x (ι i)) = l i := by
  classical

  have hstep : ∀ (i : J) (a : K) (k : ℕ) (g : V),
      ((h i - σ a • 1) ^ k) (j g) = j (((op (ι i) - a • 1) ^ k) g) := by
    intro i a k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
      simp [hj, map_smulₛₗ]
  have himg : ∀ x, ∀ f ∈ Formalism.L2.Col.eigAt op x, j f ∈ Formalism.L2.Col.eigAt h (fun i => σ (x (ι i))) := by
    intro x f hf
    rw [Formalism.L2.Col.eigAt, Submodule.mem_iInf] at hf ⊢
    intro i
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 (hf (ι i))
    exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, by rw [hstep, hk, map_zero]⟩
  set T : Submodule ℂ H := ⨆ (x : I → K) (_ : C x), Formalism.L2.Col.eigAt h (fun i => σ (x (ι i))) with hT
  have hle : Formalism.L2.Col.eigSum op C ≤ T.comap j := by
    refine iSup₂_le fun x hx f hf => ?_
    exact (le_iSup₂_of_le (f := fun (x : I → K) (_ : C x) => Formalism.L2.Col.eigAt h (fun i => σ (x (ι i)))) x hx le_rfl)
      (himg x f hf)
  have hvT : v ∈ T := by
    refine (Submodule.span_le.2 ?_) hv
    rintro _ ⟨f, hf, rfl⟩
    exact hle hf
  have hvl : v ∈ Formalism.L2.Col.eigAt h l := Formalism.L2.Col.mem_eigAt_of_forall_apply he
  by_contra hno
  push_neg at hno
  have hT' : T ≤ ⨆ (y : J → ℂ) (_ : y ≠ l), Formalism.L2.Col.eigAt h y := by
    refine iSup₂_le fun x hx => ?_
    obtain ⟨i, hi⟩ := hno x hx
    exact le_iSup₂_of_le (f := fun (y : J → ℂ) (_ : y ≠ l) => Formalism.L2.Col.eigAt h y) (fun i => σ (x (ι i)))
      (fun e => hi (congrFun e i)) le_rfl
  exact hv0 ((Submodule.disjoint_def.1 (Formalism.L2.Col.iSupIndep_eigAt hc l)) v hvl (hT' hvT))

theorem dualLab_dualLab (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, List.map_map]


set_option maxHeartbeats 1000000 in
theorem hecke_polys_of_carries : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) → ∀ p c, R.Carries p c → ∀ P ∈ A3.A.ok A3.A.μ0, RealDat.polE (A := A3.A) p.1.1 P = Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) (fun k => c (R.pl P) (dualLab (splitLab D.R.r k))) ∧ RealDat.polW (A := A3.A) p.1.1 P = Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) (fun k => c (R.pl P) (splitLab D.R.r k)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hI hok hW hEx hS hinj p c hcar P hP
  obtain ⟨hC, hSF, hEE, -⟩ := _root_.GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  obtain ⟨hG, hcj, hq⟩ := (_root_.GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.lev).2.2.2 hC.fam A3.A.μ0 P hP
  have hq0 : (A3.A.q P : ℂ) ≠ 0 := by
    rw [hq, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact (R.pl P).ne_bot
  obtain ⟨_, _, _, htie⟩ := hC.fam.tie
  obtain ⟨-, hr, ht⟩ := htie.ranks
  have hrX : D.sp.X'.rank = A3.A.r + D.R.m * A3.A.t := by rw [D.sp.X'_rank, hr, ht]; rfl
  have hrY : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _), Nat.zero_min]; simp [Ranks.rankY]
  have hr0 : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hm0 : 0 < D.R.m := by have := D.R.two_le_m; omega

  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcar.1
  have hwp : w ∈ R.EEp3 p :=
    (le_iSup₂ (f := fun c (_ : R.Carries p c) => R.EEc c) c hcar) hw
  have hv0 : LinearMap.adjoint (R.Th A3.A.μ0) w ≠ 0 := fun h0 => hw0 (hinj p w hwp h0)
  have hwE : w ∈ EEc R.toRealDat R.SF c := (hEE c) ▸ hw
  obtain ⟨hX, hXo, hXn⟩ := (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hC.lev hC.fam hC.models).1 A3.A.μ0
  obtain ⟨zE, hmE, hpE⟩ := _root_.GlobalTheory.Hk3.SplitChain.exists_transfer R.toRealDat F.lv2 hI hC hS A3.A.μ0 ⟨P, hP⟩
  have heig : ∀ k : Fin (D.sp.X'.rank + 1), hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1)
      (LinearMap.adjoint (R.Th A3.A.μ0) w) = GlobalTheory.Hk3.evC (Yc D 0) (R.pl P) (fun d => c (R.pl P) (dualLab d))
        (GlobalTheory.Hk3.splitC (Yc D 0).rank (zE k)) • LinearMap.adjoint (R.Th A3.A.μ0) w := fun k =>
    (_root_.GlobalTheory.Hk3.SysE.matched_commute R.toRealDat F.lv2 hC hS R.SF hSF A3.A.μ0 (R.pl P) hG _ _ (hmE k (Nat.lt_succ_iff.1 k.2)) hX hXo).2 c w hwE
  obtain ⟨x, hx, hxe⟩ := exists_sys_of_mem_span D.what₂.embLL (A3.rowI A3.A.μ0).opAll (R.jX A3.A.μ0)
    (fun k : Fin (D.sp.X'.rank + 1) => hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1))
    (fun k => Sum.inl ((⟨P, hP⟩ : A3.A.ok A3.A.μ0), (k : ℕ)))
    (fun k f => (_root_.GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hC.lev hC.fam hC.models).1 A3.A.μ0 hX hXo ⟨P, hP⟩ k
      (Nat.lt_succ_iff.1 k.2) f)
    (fun k k' => hXn.1 _ _ hG hG _ _) _ _ (hcar.2 (Submodule.mem_map_of_mem hw)) hv0 _ heig

  have hE : (p.1.1 P).map D.what₂.embLL =
      (Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) fun j => c (R.pl P) (dualLab (splitLab D.R.r j))).comp
        (C ((A3.A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) * X) := by
    have h1 := hpE fun j => c (R.pl P) (dualLab (splitLab (Yc D 0).rank j))
    have h2 : (Formalism.L2.Col.heckePolyOf (A3.A.r + D.R.m * A3.A.t) (A3.A.q P) fun k => x (Sum.inl (⟨P, hP⟩, k))) =
        p.1.1 P * (A3.A.fam.R A3.A.μ0).blockProd ⟨P, hP⟩ := hx.1 ⟨P, hP⟩
    have h3 := congrArg (Polynomial.map D.what₂.embLL) h2
    rw [Formalism.L2.Col.map_heckePolyOf, Polynomial.map_mul, ← hrX] at h3
    rw [GlobalTheory.Hk3.Link.heckePolyOf_congr _ _ (b := fun k => D.what₂.embLL (x (Sum.inl (⟨P, hP⟩, k)))) ?_, h3, hrY] at h1
    · refine mul_right_cancel₀ ?_ h1
      rw [Ne, Polynomial.map_eq_zero]
      unfold BlockDat.blockProd
      refine List.prod_ne_zero fun h => ?_
      obtain ⟨ν, -, hν⟩ := List.mem_map.1 h
      exact GlobalTheory.Hk3.Link.blockPoly_ne_zero _ _ _ hν
    · intro k hk
      have h5 := hxe ⟨k, Nat.lt_succ_iff.2 hk⟩
      exact (h5.trans (GlobalTheory.Hk3.Link.evC_splitC (Yc D 0) (R.pl P) hcj _ _)).symm

  obtain ⟨h, hEo, -, -, hev, -⟩ := _root_.GlobalTheory.Hk3.OpsRows.exists_opsE R.toRealDat F.lv2 hC hS R.SF hSF
  have hne : R.HE.e w ≠ 0 := fun h0 => hw0 ((hC.models.HE).1 (h0.trans (map_zero _).symm))
  obtain ⟨v, hv⟩ : ∃ v, R.HE.e w v ≠ 0 := by
    by_contra hcon
    exact hne (MultilinearMap.ext fun v => not_not.1 fun hv => hcon ⟨v, hv⟩)
  obtain ⟨cc, hβ⟩ := hC.lev.βY 0 hm0
  have hlev := (_root_.GlobalTheory.LevOp.level_operators (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβ (R.pl P)
    (by
      have hN := ((_root_.GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.lev).2.1 A3.A.μ0 (R.pl P) hG).1
      rw [Nat.cast_pow]
      intro hmem
      rcases Nat.eq_zero_or_pos cc with h0 | h0
      · rw [h0, pow_zero] at hmem
        exact (R.pl P).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hmem)
      · exact hN ((R.pl P).isPrime.mem_of_pow_mem _ hmem))
    (fun PP hPP => hG PP (Or.inl (hPP.resolve_right (Finset.notMem_empty _))))).1
  have hm := (Submodule.mem_inf.1 (Submodule.mem_comap.1 hwE)).1
  have hrel := GlobalTheory.Hk3.Link.eig_rel (Yc D 0) (R.pl P) hcj _ hv (fun k hk g =>
      (GlobalTheory.Hk3.Link.mult_lev R.θ _ _ _ _ hm v k (hlev k hk).1 g).trans
        ((congrArg (fun z : ℂ => z * R.HE.e w v g) (hlev k hk).2).trans (one_mul _)))
      (fun d => c (R.pl P) (dualLab d)) (fun d hd => by
      have h5 := (hEo (R.pl P) hG (Finsupp.single d 1) w).symm.trans
        ((congrArg R.HE.e (hev c _ hG (Finsupp.single d 1) w hwE)).trans (map_smul _ _ _))
      exact congrArg (fun U : MMap (R.MY 0) => U v) (h5.trans
        (congrArg (fun z : ℂ => z • R.HE.e w) (GlobalTheory.Hk3.Link.evC_single (Yc D 0) (R.pl P) _ d hd))))
  rw [hrY] at hrel
  simp only [dualLab_dualLab] at hrel
  obtain ⟨hb0, hab⟩ := hrel
  have hrr : c (R.pl P) (splitLab D.R.r D.R.r) * c (R.pl P) (dualLab (splitLab D.R.r D.R.r)) = 1 := by
    rw [hab D.R.r le_rfl, Nat.sub_self, hb0]
  have hbr : c (R.pl P) (dualLab (splitLab D.R.r D.R.r)) ≠ 0 := right_ne_zero_of_mul_eq_one hrr
  have ha0 : c (R.pl P) (splitLab D.R.r 0) = 1 := by
    have := hab 0 (Nat.zero_le _)
    rw [Nat.sub_zero] at this
    exact mul_right_cancel₀ hbr (this.trans (one_mul _).symm)
  have hba : ∀ j, j ≤ D.R.r → c (R.pl P) (dualLab (splitLab D.R.r j)) * c (R.pl P) (splitLab D.R.r D.R.r) =
      c (R.pl P) (splitLab D.R.r (D.R.r - j)) := by
    intro j hj
    have := hab (D.R.r - j) (Nat.sub_le _ _)
    rw [Nat.sub_sub_self hj] at this
    rw [← this, mul_assoc, mul_comm _ (c (R.pl P) (splitLab D.R.r D.R.r)), hrr, mul_one]
  have hdual := _root_.GlobalTheory.Hk3.DualHecke.dualPoly_heckePolyOf_comp ℂ D.R.r (A3.A.q P) (fun j => c (R.pl P) (splitLab D.R.r j))
    (fun j => c (R.pl P) (dualLab (splitLab D.R.r j))) ((A3.A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) 1 hq0
    (pow_ne_zero _ hq0) hr0 ha0 hba
  have hs0 : ((A3.A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) ≠ 0 := pow_ne_zero _ hq0
  constructor
  · unfold RealDat.polE
    rw [hE, Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ hs0, C_1, one_mul, Polynomial.comp_X]
  · unfold RealDat.polW
    rw [GlobalTheory.Hk3.Link.dualPoly_map, hE, map_pow, map_natCast]
    have hsc : (A3.A.q P : ℂ) ^ (D.R.r - 1 + D.R.m / 2 * D.R.t) =
        (A3.A.q P : ℂ) ^ (D.R.m / 2 * D.R.t) * 1 * (A3.A.q P : ℂ) ^ (D.R.r - 1) := by
      rw [pow_add]; ring
    rw [hsc, hdual, C_1, one_mul, Polynomial.comp_X]

end GlobalTheory.CarriedHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergAnnihilationCreationCommutatorEqDelta
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock.CommDM
open GlobalTheory.CCRFock

private lemma unitAt_apply_eq_ite {W : Type} [DecidableEq W] {P Q R S : ℕ} (j : W × (Ix P Q × Ix R S)) (z : ℂ)
    (w : W) (a : Ix P Q) (b : Ix R S) : unitAt j z w a b = if (w, (a, b)) = j then z else 0 := by
  obtain ⟨j1, j2, j3⟩ := j
  by_cases h1 : w = j1
  · subst h1
    by_cases h2 : a = j2
    · subst h2
      by_cases h3 : b = j3
      · subst h3
        simp [unitAt]
      · simp [unitAt, h3, Ne.symm h3]
    · simp [unitAt, h2, Ne.symm h2]
  · simp [unitAt, h1]

theorem sum_unitAt {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ} (j k : W × (Ix P Q × Ix R S)) (z z' : ℂ) :
    (∑ w, ∑ a, ∑ b, lineSign a b * unitAt j z w a b * star (unitAt k z' w a b)) =
      if j = k then lineSign j.2.1 j.2.2 * z * star z' else 0 := by
  have key : ∀ (w : W) (a : Ix P Q) (b : Ix R S), lineSign a b * unitAt j z w a b * star (unitAt k z' w a b) =
      if (w, (a, b)) = j then (if j = k then lineSign j.2.1 j.2.2 * z * star z' else 0) else 0 := by
    intro w a b
    rw [unitAt_apply_eq_ite, unitAt_apply_eq_ite]
    by_cases hj : (w, (a, b)) = j
    · subst hj
      by_cases hk : (w, (a, b)) = k
      · subst hk
        simp
      · simp [hk]
    · simp [hj]
  simp only [key]
  rw [Fintype.sum_eq_single j.1, Fintype.sum_eq_single j.2.1, Fintype.sum_eq_single j.2.2]
  all_goals first
    | (intro x hx; simp [Prod.ext_iff, hx])
    | simp

theorem lineSign_cases {P Q R S : ℕ} (a : Ix P Q) (b : Ix R S) : (lineSign a b : ℂ) = 1 ∨ (lineSign a b : ℂ) = -1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem comm_expand {V : Type} [AddCommGroup V] [Module ℂ V] (A A' B B' : Module.End ℂ V) (c u v : ℂ) :
    -(c • (A + u • A')) * (c • (B - v • B')) - (c • (B - v • B')) * -(c • (A + u • A')) =
      -((c * c) • ((A * B - B * A) - v • (A * B' - B' * A) + u • (A' * B - B * A') - (u * v) • (A' * B' - B' * A'))) := by
  simp only [neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_smul, mul_add, add_mul, mul_sub, sub_mul,
    smul_add, smul_sub, smul_neg]
  module

theorem inv_sq : (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ * (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ =
    (8 * (Real.pi : ℂ))⁻¹ := by
  rw [← mul_inv]
  congr 1
  have h : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  linear_combination 4 * h

theorem fockD_fockM_comm : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ j k : W × (Ix P Q × Ix R S), GlobalTheory.CCRFock.fockD H j * GlobalTheory.CCRFock.fockM H k - GlobalTheory.CCRFock.fockM H k * GlobalTheory.CCRFock.fockD H j =
      if j = k then 1 else 0 := by
  intro V _ _ W _ _ P Q R S H _ _ hcomm j k
  simp only [GlobalTheory.CCRFock.fockD, GlobalTheory.CCRFock.fockM]
  rw [comm_expand, hcomm, hcomm, hcomm, hcomm, sum_unitAt, sum_unitAt, sum_unitAt, sum_unitAt, inv_sq]
  by_cases hjk : j = k
  · subst hjk
    rcases lineSign_cases j.2.1 j.2.2 with h | h
    · simp only [if_true, h]
      match_scalars
      simp
      field_simp
      ring_nf
      simp [Complex.I_sq]
    · simp only [if_true, h]
      match_scalars
      simp
      field_simp
      ring_nf
      simp [Complex.I_sq]
  · simp [hjk]

end GlobalTheory.CCRFock.CommDM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCreationOperatorsCommuteOfCcr
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem fockM_comm_sum {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ} (j k : W × (Ix P Q × Ix R S)) (z z' : ℂ) :
    (∑ w, ∑ a, ∑ b, lineSign a b * unitAt j z w a b * star (unitAt k z' w a b)) =
      if j = k then lineSign j.2.1 j.2.2 * z * star z' else 0 := by
  obtain ⟨w, a, b⟩ := j
  obtain ⟨w', a', b'⟩ := k
  rw [Finset.sum_eq_single w, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · by_cases hw : w = w'
    · subst hw
      by_cases ha : a = a'
      · subst ha
        by_cases hb : b = b'
        · subst hb; simp [unitAt]
        · simp [unitAt, hb, Ne.symm hb]
      · simp [unitAt, ha, Ne.symm ha]
    · simp [unitAt, hw]
  · intro c _ hc; simp [unitAt, Ne.symm hc]
  · simp
  · intro c _ hc; simp [unitAt, Ne.symm hc]
  · simp
  · intro c _ hc; simp [unitAt, hc]
  · simp

theorem fockM_comm : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ j k : W × (Ix P Q × Ix R S), GlobalTheory.CCRFock.fockM H j * GlobalTheory.CCRFock.fockM H k = GlobalTheory.CCRFock.fockM H k * GlobalTheory.CCRFock.fockM H j := by
  intro V _ _ W _ _ P Q R S H _ _ hc j k
  have h11 := hc (unitAt j 1) (unitAt k 1)
  have h1i := hc (unitAt j 1) (unitAt k Complex.I)
  have hi1 := hc (unitAt j Complex.I) (unitAt k 1)
  have hii := hc (unitAt j Complex.I) (unitAt k Complex.I)
  rw [fockM_comm_sum] at h11 h1i hi1 hii
  by_cases hjk : j = k
  · rw [hjk]
  · simp only [if_neg hjk, Complex.zero_im, Complex.ofReal_zero, mul_zero, zero_smul, sub_eq_zero] at h11 h1i hi1 hii
    unfold fockM
    have c : Commute (H (unitAt j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAt j Complex.I))
        (H (unitAt k 1) - (lineSign k.2.1 k.2.2 * Complex.I) • H (unitAt k Complex.I)) :=
      Commute.sub_left (Commute.sub_right h11 (Commute.smul_right h1i _))
        (Commute.smul_left (Commute.sub_right hi1 (Commute.smul_right hii _)) _)
    exact ((c.smul_left _).smul_right _).eq

end GlobalTheory.CCRFock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivativeOnSchwartzTensorConj
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory

theorem heisenbergDeriv_tensor_conj (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a₁ b₁ a₂ b₂ : κ → AF F)
    (f g₁ g₂ : SInf F κ) (f₀ h : SInf F (κ ⊕ κ))
    (hg₁ : ∀ y, g₁ y = fderiv ℝ f y (fun i => evI F (a₁ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₁ i)) : ℝ) * f y)
    (hg₂ : ∀ y, g₂ y = fderiv ℝ f y (fun i => evI F (a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₂ i)) : ℝ) * f y)
    (hh : ∀ x, h x = fderiv ℝ f₀ x (fun i => evI F (Sum.elim a₁ a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F (Sum.elim b₁ (-b₂) i)) : ℝ) * f₀ x)
    (hf₀ : ∀ x, f₀ x = f (x ∘ Sum.inl) * star (f (x ∘ Sum.inr))) (x : κ ⊕ κ → mixedEmbedding.mixedSpace F) :
    h x = g₁ (x ∘ Sum.inl) * star (f (x ∘ Sum.inr)) + f (x ∘ Sum.inl) * star (g₂ (x ∘ Sum.inr)) := by
  let L₁ : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) := ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Sum.inl i))
  let L₂ : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) := ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Sum.inr i))
  have hL₁ : ∀ y, L₁ y = y ∘ Sum.inl := fun y => rfl
  have hL₂ : ∀ y, L₂ y = y ∘ Sum.inr := fun y => rfl
  have hfun : (f₀ : (κ ⊕ κ → mixedEmbedding.mixedSpace F) → ℂ) = fun y => f (L₁ y) * Complex.conjCLE (f (L₂ y)) := by
    funext y; rw [hf₀]; rfl
  have hd₁ : HasFDerivAt (fun y => f (L₁ y)) ((fderiv ℝ f (L₁ x)).comp L₁) x :=
    (f.differentiableAt.hasFDerivAt).comp x L₁.hasFDerivAt
  have hd₂ : HasFDerivAt (fun y => Complex.conjCLE (f (L₂ y)))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℝ f (L₂ x)).comp L₂)) x :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x ((f.differentiableAt.hasFDerivAt).comp x L₂.hasFDerivAt)
  have hD : fderiv ℝ f₀ x = f (L₁ x) • ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℝ f (L₂ x)).comp L₂)) + Complex.conjCLE (f (L₂ x)) • ((fderiv ℝ f (L₁ x)).comp L₁) := by
    rw [hfun]
    exact (hd₁.mul hd₂).fderiv
  have hevneg : ∀ b : AF F, evI F (-b) = - evI F b := by
    intro b
    unfold evI
    rw [show (-b).1 = -b.1 from rfl, map_neg]
  have htr : (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F (Sum.elim b₁ (-b₂) i)) : ℝ)
      = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, (x ∘ Sum.inl) i * evI F (b₁ i))
        - Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, (x ∘ Sum.inr) i * evI F (b₂ i)) := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, hevneg, mul_neg, Finset.sum_neg_distrib,
      map_add, map_neg, Function.comp_apply]
    ring
  rw [hh x, hg₁, hg₂, hD, htr, hf₀]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, hL₁, hL₂, smul_eq_mul]
  have e1 : ((fun i => evI F (Sum.elim a₁ a₂ i)) ∘ Sum.inl) = fun i => evI F (a₁ i) := rfl
  have e2 : ((fun i => evI F (Sum.elim a₁ a₂ i)) ∘ Sum.inr) = fun i => evI F (a₂ i) := rfl
  rw [e1, e2]
  simp only [star_sub, star_mul', Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFamilyExpandCreationAnnihilation
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem lineSign_mul_self {P Q R S : ℕ} (a : Ix P Q) (b : Ix R S) : lineSign a b * lineSign a b = 1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem sum_unitAt {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ} (c : W → Matrix (Ix P Q) (Ix R S) ℂ) :
    c = ∑ j : W × (Ix P Q × Ix R S), unitAt j (c j.1 j.2.1 j.2.2) := by
  rw [Fintype.sum_prod_type]
  conv_lhs => rw [← Finset.univ_sum_single c]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Fintype.sum_prod_type]
  conv_lhs => rw [Matrix.matrix_eq_sum_single (c w)]
  funext v
  simp only [unitAt, Finset.sum_apply]
  by_cases h : v = w
  · subst h
    simp
  · simp [h]

theorem unitAt_re_im {W : Type} [DecidableEq W] {P Q R S : ℕ} (j : W × (Ix P Q × Ix R S)) (z : ℂ) :
    unitAt j z = ((z.re : ℝ) : ℂ) • unitAt j 1 + ((z.im : ℝ) : ℂ) • unitAt j Complex.I := by
  simp only [unitAt, ← Pi.single_smul', ← Pi.single_add, Matrix.smul_single, ← Matrix.single_add, smul_eq_mul, mul_one,
    Complex.re_add_im]

theorem heis_expand : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    ∀ c : W → Matrix (Ix P Q) (Ix R S) ℂ, H c = ∑ j : W × (Ix P Q × Ix R S),
      ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • GlobalTheory.CCRFock.fockM H j +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • GlobalTheory.CCRFock.fockD H j) := by
  intro V _ _ W _ _ P Q R S H hadd hsmul c
  have h0 : H 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  let H' : (W → Matrix (Ix P Q) (Ix R S) ℂ) →+ Module.End ℂ V := ⟨⟨H, h0⟩, hadd⟩
  have hsum : H c = ∑ j : W × (Ix P Q × Ix R S), H (unitAt j (c j.1 j.2.1 j.2.2)) := by
    conv_lhs => rw [sum_unitAt c]
    exact map_sum H' _ _
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [unitAt_re_im, hadd, hsmul, hsmul]
  have hs : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast this.ne'
  have he := lineSign_mul_self j.2.1 j.2.2
  unfold fockM fockD coefM coefD
  generalize ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = s at hs ⊢
  generalize lineSign j.2.1 j.2.2 = e at he ⊢
  generalize H (unitAt j 1) = A
  generalize H (unitAt j Complex.I) = B
  generalize ((c j.1 j.2.1 j.2.2).re : ℂ) = x
  generalize ((c j.1 j.2.1 j.2.2).im : ℂ) = y
  have hI := Complex.I_mul_I
  match_scalars
  · field_simp
    ring
  · field_simp
    linear_combination (2 * y * e * e) * hI - 2 * y * he

end GlobalTheory.CCRFock
end

