module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.PointRingCommRing
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0214
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormZpowSubOneLeBis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0213
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0212
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHomModuloUnramifiedShapeOfLocalDuality

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveOfSumFor
section
namespace GlobalTheory.WachUse

open GlobalTheory.WachUse Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n}

theorem additive_of_sumFor (hW : GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.SumFor W) : Additive W := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.SumFor at hW
  intro T T' S f g hT hT' hb hs z hz
  obtain ⟨σ, hσ, -, -, hmem⟩ := hW T T' S hT hT' f g (by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.IsSumLat
    exact ⟨hb, hs⟩)

  set p := σ.symm z with hp
  have hz' : σ (p.1, p.2) = z := by simp [hp]
  rw [← hz'] at hz
  obtain ⟨hx, hy⟩ := (hmem p.1 p.2).1 hz
  exact ⟨p.1, hx, p.2, hy, by rw [← hz', hσ]⟩

end Generic

theorem additive_of_caseA : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P)
    (E : LocFon l P AI H) (C : LocCmpT l P AI H E), ∀ (K LL : FinExt l) (h : CaseA K LL),
    Additive (H.W K 1 LL h.2.2) := by
  intro l _ P _ H _ _ K LL h

  exact additive_of_sumFor (GlobalTheory.WachSum.sumPart l P H K 1 LL h.2.2)

end GlobalTheory.WachUse
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalProdEqZeroHodgeTateCyclotomicFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.CycEigen

theorem aeval_eq_zero_of_eigenbasis {C : Type} [Field C] {r : ℕ} (A : Matrix (Fin r) (Fin r) C)
    (e : Fin r → Fin r → C) (he : LinearIndependent C e) (c : Fin r → C)
    (hc : ∀ k, A.mulVec (e k) = c k • e k) (P : Polynomial C) (hP : ∀ k, P.eval (c k) = 0) :
    Polynomial.aeval A P = 0 := by
  have h1 : ∀ k, (Polynomial.aeval A P).mulVec (e k) = 0 := by
    intro k
    have h2 : Matrix.toLinAlgEquiv' (Polynomial.aeval A P) (e k) = P.eval (c k) • e k := by
      rw [← Polynomial.aeval_algHom_apply]
      exact Module.End.aeval_apply_of_mem_apply_eq_smul (by simpa using hc k)
    rw [hP, zero_smul] at h2
    simpa using h2
  have hsp : Submodule.span C (Set.range e) = ⊤ :=
    he.span_eq_top_of_card_eq_finrank' (by simp)
  have h3 : Matrix.toLin' (Polynomial.aeval A P) = 0 :=
    LinearMap.ext_on_range hsp fun k => by simpa using h1 k
  simpa using h3

variable {l : ℕ} [Fact l.Prime]

theorem hinf_le_gj (K : FinExt l) (s : ℕ) : Hinf K ≤ Gj K s :=
  IntermediateField.fixingSubgroup_antitone
    (sup_le_sup_left (IntermediateField.adjoin.mono ℚ_[l] {x : Om l | x ^ (l ^ s) = 1}
      {x : Om l | ∃ j : ℕ, x ^ (l ^ j) = 1} fun (x : Om l) (hx : x ^ (l ^ s) = 1) =>
      (⟨s, hx⟩ : ∃ j : ℕ, x ^ (l ^ j) = 1)) _ : Ks K s ≤ Kinf K)

theorem gj_le (K : FinExt l) (s : ℕ) : Gj K s ≤ (K0 K).fixingSubgroup :=
  IntermediateField.fixingSubgroup_antitone (show K0 K ≤ Ks K s from le_sup_left)

theorem norm_l_lt : ‖(l : PadicComplex l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicComplex l)), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem norm_chiC {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (j : ℤ) (g : GQ l) : ‖chiC χ j g‖ = 1 := by
  rw [chiC, norm_algebraMap', Units.val_zpow_eq_zpow_val, norm_zpow,
    (GlobalTheory.Cyc.cyc_basic l χ hχ).1, one_zpow]

theorem chiC_hinf {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) (j : ℤ) {h : GQ l}
    (hh : h ∈ Hinf K) : chiC χ j h = 1 := by
  have : χ h = 1 :=
    ((GlobalTheory.Cyc.cyc_basic l χ hχ).2.2 K h (gj_le K 0 (hinf_le_gj K 0 hh))).2.1 hh
  simp [chiC, this]

theorem chiC_neg_mul (χ : GQ l →* ℚ_[l]ˣ) (j : ℤ) (g : GQ l) :
    chiC χ (-j) g * chiC χ j g = 1 := by
  rw [chiC, chiC, ← map_mul, ← Units.val_mul, ← zpow_add]
  simp

theorem eigen_of_norm_le {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
    {χ : GQ l →* ℚ_[l]ˣ} (hact : IsActC act) (hχ : IsCyc χ) {K : FinExt l} {m r : ℕ}
    (hm : Lev l m) {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l}
    (hF : Frame χ K m U g) (u : ℤ) (y : Fin r → PadicComplex l) (hy1 : ∀ a, ‖y a‖ ≤ 1)
    (hy : ∀ σ ∈ Gj K m, twAct act χ u U σ y = y) : chiC χ u g • (U g).mulVec y = y := by
  obtain ⟨hg, -, hU, -, hH, hU1⟩ := hF
  obtain ⟨hdec, hdir, -, hmul, hstab, -⟩ := GlobalTheory.TateDecomp.tate_decomposition l act χ hact hχ K m hm.1
  have hO : ∀ a, y a ∈ Ohat K := by
    intro a
    refine (_root_.GlobalTheory.CycInvariants.fixed_iff_mem_Ohat l act hact K (y a) (hy1 a)).1 fun h hh => ?_
    have := congrFun (hy h (hinf_le_gj K m hh)) a
    simpa [twAct, chiC_hinf hχ K u hh, hH h hh] using this
  choose y0 hy0 x hx hsum using fun a => hdec (y a) (hO a)
  have hfix : (fun a => act g (y0 a)) = y0 := funext fun a => act_inC hact hg.1 (hy0 a).1
  have hyx : y = y0 + x := funext hsum
  have hadd : twAct act χ u U g y = twAct act χ u U g y0 + twAct act χ u U g x := by
    have e : (fun a => act g (y a)) = (fun a => act g (y0 a)) + fun a => act g (x a) := by
      funext a; rw [hsum a, map_add (f := _)]; rfl
    simp only [twAct]
    rw [e, Matrix.mulVec_add, smul_add]
  have hc : chiC χ u g ∈ intC (Ks K m) := ⟨chiC_mem_inC χ u g _, (norm_chiC hχ u g).le⟩
  have hX : ∀ a, twAct act χ u U g x a ∈ Xj K m := by
    intro a
    simp only [twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact hmul _ hc _ ((Xj K m).sum_mem fun b _ =>
      hmul _ (hU g hg.1 a b) _ (hstab g (gj_le K m hg.1) _ (hx b)))
  have hK : ∀ a, twAct act χ u U g y0 a - y0 a ∈ inC (Ks K m) := by
    intro a
    rw [mem_inC_iff]
    simp only [twAct, hfix, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact sub_mem (mul_mem ((mem_inC_iff _ _).1 hc.1) (sum_mem fun b _ =>
      mul_mem ((mem_inC_iff _ _).1 (hU g hg.1 a b).1) ((mem_inC_iff _ _).1 (hy0 b).1)))
      ((mem_inC_iff _ _).1 (hy0 a).1)
  have hrel : ∀ a, twAct act χ u U g y0 a - y0 a = x a - twAct act χ u U g x a := by
    intro a
    have h1 := congrFun (hadd.symm.trans (hy g hg.1)) a
    rw [Pi.add_apply, hsum a] at h1
    linear_combination h1
  have hzero : ∀ a, twAct act χ u U g y0 a - y0 a = 0 := fun a =>
    hdir _ (hK a) _ ((Xj K m).sub_mem (hx a) (hX a)) 0 (by rw [pow_zero, one_mul]; exact hrel a)
  have hx0 : x = 0 := by
    refine twAct_fixed_eq_zero hact hχ hm hg U (hU g hg.1) hU1 u x hx ?_
    funext a
    exact (sub_eq_zero.1 ((hrel a).symm.trans (hzero a))).symm
  rw [hx0, add_zero] at hyx
  have h2 := hy g hg.1
  rw [hyx] at h2 ⊢
  rwa [twAct, hfix] at h2

theorem eigen_of_fixed {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
    {χ : GQ l →* ℚ_[l]ˣ} (hact : IsActC act) (hχ : IsCyc χ) {K : FinExt l} {m r : ℕ}
    (hm : Lev l m) {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)} {g : GQ l}
    (hF : Frame χ K m U g) (u : ℤ) (y : Fin r → PadicComplex l)
    (hy : ∀ σ ∈ Gj K m, twAct act χ u U σ y = y) : (U g).mulVec y = chiC χ (-u) g • y := by
  have hl0 : (l : PadicComplex l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (x := (‖y‖ + 1)⁻¹) (by positivity) (norm_l_lt (l := l))
  have h1 : ∀ a, ‖(((l : PadicComplex l) ^ N) • y) a‖ ≤ 1 := by
    intro a
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    calc _ ≤ (‖y‖ + 1)⁻¹ * (‖y‖ + 1) :=
          mul_le_mul hN.le ((norm_le_pi_norm y a).trans (by linarith)) (norm_nonneg _)
            (by positivity)
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have h2 := eigen_of_norm_le hact hχ hm hF u _ h1 (by
    intro σ hσ
    have e : (fun a => act σ ((((l : PadicComplex l) ^ N) • y) a))
        = ((l : PadicComplex l) ^ N) • fun a => act σ (y a) := by
      funext a; simp
    have := hy σ hσ
    rw [twAct] at this ⊢
    rw [e, Matrix.mulVec_smul, smul_comm, this])
  rw [Matrix.mulVec_smul, smul_comm] at h2
  have h3 := smul_right_injective _ (pow_ne_zero N hl0) h2
  calc (U g).mulVec y = (chiC χ (-u) g * chiC χ u g) • (U g).mulVec y := by
        rw [chiC_neg_mul, one_smul]
    _ = _ := by rw [mul_smul, h3]

theorem aeval_prod_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → Polynomial.aeval (U g) (∏ u ∈ J, (Polynomial.X - Polynomial.C (chiC χ (-u) g))) = 0 := by
  intro l _ act χ hact hχ K m r hm U g hF J ⟨e, u, he, hu, hfix⟩
  refine aeval_eq_zero_of_eigenbasis (U g) e he (fun k => chiC χ (-(u k)) g)
    (fun k => eigen_of_fixed hact hχ hm hF (u k) (e k) fun σ hσ => hfix σ hσ k) _ fun k => ?_
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_coe.1 (hu k)) (by simp)

end GlobalTheory.CycEigen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLatticeQuotPrimePow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.LatticeCard

theorem mem_span_singleton_smul_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : R) (x : M) : x ∈ (Ideal.span {b} • ⊤ : Submodule R M) ↔ ∃ y : M, b • y = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem card_quot_pow_succ {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (ha : IsSMulRegular M a) (k : ℕ) :
    Nat.card (M ⧸ (Ideal.span {a ^ (k + 1)} • ⊤ : Submodule R M)) =
      Nat.card (M ⧸ (Ideal.span {a} • ⊤ : Submodule R M)) *
      Nat.card (M ⧸ (Ideal.span {a ^ k} • ⊤ : Submodule R M)) := by
  set S : Submodule R M := Ideal.span {a ^ (k + 1)} • ⊤ with hS
  set T : Submodule R M := Ideal.span {a ^ k} • ⊤ with hT
  have hST : S ≤ T := by
    intro x hx
    rw [hS, mem_span_singleton_smul_top] at hx
    rw [hT, mem_span_singleton_smul_top]
    obtain ⟨y, rfl⟩ := hx
    exact ⟨a • y, by rw [smul_smul, ← pow_succ]⟩
  have h1 := Submodule.card_eq_card_quotient_mul_card (T.map S.mkQ)
  rw [Nat.card_congr (Submodule.quotientQuotientEquivQuotient S T hST).toEquiv] at h1
  rw [h1]
  congr 1
  have hmem : ∀ x : M, S.mkQ (a ^ k • x) ∈ T.map S.mkQ := fun x =>
    ⟨a ^ k • x, SetLike.mem_coe.2 ((mem_span_singleton_smul_top _ _).2 ⟨x, rfl⟩), rfl⟩
  let φ : M →ₗ[R] ↥(T.map S.mkQ) :=
    LinearMap.codRestrict (T.map S.mkQ) (S.mkQ ∘ₗ (a ^ k • LinearMap.id)) (fun x => hmem x)
  have hsurj : Function.Surjective φ := by
    rintro ⟨z, w, hw, rfl⟩
    rw [SetLike.mem_coe, mem_span_singleton_smul_top] at hw
    obtain ⟨x, rfl⟩ := hw
    exact ⟨x, rfl⟩
  have hker : LinearMap.ker φ = (Ideal.span {a} • ⊤ : Submodule R M) := by
    ext x
    rw [LinearMap.mem_ker, mem_span_singleton_smul_top]
    have hφ : φ x = 0 ↔ a ^ k • x ∈ S := by
      rw [← Subtype.coe_inj]
      change S.mkQ (a ^ k • x) = 0 ↔ _
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [hφ, hS, mem_span_singleton_smul_top]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, (ha.pow k) ?_⟩
      change a ^ k • (a • y) = a ^ k • x
      rw [smul_smul, ← pow_succ]; exact hy
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [smul_smul, ← pow_succ]⟩
  rw [← Nat.card_congr (LinearMap.quotKerEquivOfSurjective φ hsurj).toEquiv,
    Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv]

theorem card_quot_pow {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (ha : IsSMulRegular M a) (r : ℕ) :
    Nat.card (M ⧸ (Ideal.span {a ^ r} • ⊤ : Submodule R M)) =
      Nat.card (M ⧸ (Ideal.span {a} • ⊤ : Submodule R M)) ^ r := by
  induction r with
  | zero =>
    rw [pow_zero, pow_zero, Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨0⟩⟩
    induction x using Submodule.Quotient.induction_on with | _ x => ?_
    induction y using Submodule.Quotient.induction_on with | _ y => ?_
    rw [Submodule.Quotient.eq, mem_span_singleton_smul_top]
    exact ⟨x - y, one_smul _ _⟩
  | succ k ih => rw [card_quot_pow_succ a ha k, ih, pow_succ, mul_comm]

theorem card_quot_equiv {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (b : R) :
    Nat.card (M ⧸ (Ideal.span {b} • ⊤ : Submodule R M)) =
      Nat.card (N ⧸ (Ideal.span {b} • ⊤ : Submodule R N)) := by
  refine Nat.card_congr (Submodule.Quotient.equiv _ _ e ?_).toEquiv
  ext y
  rw [Submodule.mem_map_equiv, mem_span_singleton_smul_top, mem_span_singleton_smul_top]
  constructor
  · rintro ⟨x, hx⟩; exact ⟨e x, by rw [← map_smul, hx, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨x, rfl⟩; exact ⟨e.symm x, by rw [map_smul]⟩

theorem card_quot_fun {ι O : Type*} [Fintype ι] [CommRing O] (b : O) :
    Nat.card ((ι → O) ⧸ (Ideal.span {b} • ⊤ : Submodule O (ι → O))) =
      Nat.card (O ⧸ Ideal.span {b}) ^ Fintype.card ι := by
  let π : (ι → O) →ₗ[O] (ι → O ⧸ Ideal.span {b}) :=
    LinearMap.pi (fun i => (Ideal.Quotient.mkₐ O (Ideal.span {b})).toLinearMap ∘ₗ LinearMap.proj i)
  have hπ : ∀ x i, π x i = Ideal.Quotient.mk _ (x i) := fun x i => rfl
  have hsurj : Function.Surjective π := by
    intro y
    refine ⟨fun i => (y i).out, funext fun i => ?_⟩
    rw [hπ, Ideal.Quotient.mk_out]
  have hker : LinearMap.ker π = (Ideal.span {b} • ⊤ : Submodule O (ι → O)) := by
    ext x
    rw [LinearMap.mem_ker, mem_span_singleton_smul_top]
    constructor
    · intro hx
      have : ∀ i, ∃ c, b * c = x i := fun i => by
        have h := congrFun hx i
        rw [hπ, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
        obtain ⟨c, hc⟩ := h
        exact ⟨c, hc.symm⟩
      choose c hc using this
      exact ⟨c, funext fun i => by simp [hc]⟩
    · rintro ⟨y, rfl⟩
      funext i
      rw [hπ, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact ⟨y i, by simp⟩
  rw [← Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv,
    Nat.card_congr (LinearMap.quotKerEquivOfSurjective π hsurj).toEquiv, Nat.card_fun,
    Nat.card_eq_fintype_card (α := ι)]

end GlobalTheory.LatticeCard

namespace GlobalTheory.LatticeCard

theorem card_lattice_quot_pow : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep G ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ), Nat.card (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) = Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL A.V) := by
  intro l _ G _ _ LL _ _ _ O _ _ hG A LA r
  obtain ⟨⟨hD, -, hFr⟩, -, -, -, -⟩ := hG
  haveI := hD
  haveI := hFr
  haveI : Module.Free O LA.T := LA.free
  haveI : Module.Finite O LA.T := Module.Finite.iff_fg.2 LA.fg
  let b := Module.Free.chooseBasis O LA.T
  have hli : LinearIndependent LL (fun i => (b i : A.V)) := by
    rw [← LinearIndependent.iff_fractionRing O LL]
    exact b.linearIndependent.map' LA.T.subtype (Submodule.ker_subtype _)
  have hT : (LA.T : Set A.V) ⊆ Submodule.span LL (Set.range fun i => (b i : A.V)) := by
    intro x hx
    have hx' : (⟨x, hx⟩ : LA.T) ∈ Submodule.span O (Set.range b) := by
      rw [b.span_eq]; trivial
    have h2 := Submodule.apply_mem_span_image_of_mem_span LA.T.subtype hx'
    rw [← Set.range_comp] at h2
    exact Submodule.span_le_restrictScalars O LL _ h2
  have hsp : ⊤ ≤ Submodule.span LL (Set.range fun i => (b i : A.V)) :=
    calc ⊤ = Submodule.span LL (LA.T : Set A.V) := LA.span.symm
      _ ≤ _ := Submodule.span_le.2 hT
  have hn : finrank LL A.V = Fintype.card (Module.Free.ChooseBasisIndex O LA.T) :=
    finrank_eq_card_basis (Basis.mk hli hsp)
  have hl : ((l : ℕ) : LL) ≠ 0 := by
    have h := (algebraMap ℚ_[l] LL).injective.ne
      (show ((l : ℕ) : ℚ_[l]) ≠ 0 from Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    simpa using h
  have hreg : IsSMulRegular LA.T ((l : ℕ) : O) := by
    intro x y hxy
    have h1 : ((l : ℕ) : O) • (x : A.V) = ((l : ℕ) : O) • (y : A.V) := by
      have := congrArg (fun z : LA.T => (z : A.V)) hxy
      simpa only [Submodule.coe_smul] using this
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul LL,
      ← Nat.cast_smul_eq_nsmul LL l (y : A.V)] at h1
    exact Subtype.ext (smul_right_injective A.V hl h1)
  rw [card_quot_pow _ hreg, card_quot_equiv b.equivFun, card_quot_fun, hn, ← pow_mul, mul_comm]

end GlobalTheory.LatticeCard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEqZeroOfStable
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.UnramDisjoint

theorem coeff_eq_zero_of_stable {F Ω ι : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
    [Fintype ι] (K N : IntermediateField F Ω)
    (hN : ∀ (g : Ω ≃ₐ[F] Ω) (y : Ω), y ∈ N → g y ∈ N) (x : ι → Ω) (hx : ∀ i, x i ∈ K)
    (hind : ∀ c : ι → Ω, (∀ i, c i ∈ K ⊓ N) → ∑ i, c i * x i = 0 → ∀ i, c i = 0)
    (c : ι → Ω) (hc : ∀ i, c i ∈ N) (h : ∑ i, c i * x i = 0) : ∀ i, c i = 0 := by
  classical
  suffices H : ∀ n : ℕ, ∀ c : ι → Ω, (Finset.univ.filter (fun i => c i ≠ 0)).card = n →
      (∀ i, c i ∈ N) → ∑ i, c i * x i = 0 → ∀ i, c i = 0 from H _ c rfl hc h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hcard hc h
  by_contra hne
  obtain ⟨j, hj⟩ := not_forall.mp hne

  set d : ι → Ω := fun i => c i * (c j)⁻¹ with hd
  have hdN : ∀ i, d i ∈ N := fun i => N.mul_mem (hc i) (N.inv_mem (hc j))
  have hdj : d j = 1 := mul_inv_cancel₀ hj
  have hdsum : ∑ i, d i * x i = 0 := by
    calc ∑ i, d i * x i = (∑ i, c i * x i) * (c j)⁻¹ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by simp only [hd]; ring)
      _ = 0 := by rw [h, zero_mul]

  have hfix : ∀ g ∈ K.fixingSubgroup, ∀ i, g (d i) = d i := by
    intro g hg
    have hgx : ∀ i, g (x i) = x i := fun i => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ (hx i)
    set e : ι → Ω := fun i => g (d i) - d i with he
    have heN : ∀ i, e i ∈ N := fun i => N.sub_mem (hN g _ (hdN i)) (hdN i)
    have h2 : ∑ i, g (d i) * x i = 0 := by
      have := congrArg g hdsum
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at this
      simpa only [map_mul, hgx] using this
    have hesum : ∑ i, e i * x i = 0 := by
      simp only [he, sub_mul, Finset.sum_sub_distrib, h2, hdsum, sub_zero]
    have hej : e j = 0 := by simp only [he, hdj, map_one, sub_self]
    have hlt : (Finset.univ.filter (fun i => e i ≠ 0)).card < n := by
      rw [← hcard]
      apply Finset.card_lt_card
      refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨j, ?_, ?_⟩
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        intro hci
        apply hi
        have hdi : d i = 0 := by simp only [hd, hci, zero_mul]
        simp only [he, hdi, map_zero, sub_zero]
      · simp [hj]
      · simp [hej]
    intro i
    exact sub_eq_zero.mp (ih _ hlt e rfl heN hesum i)

  have hdK : ∀ i, d i ∈ K := by
    intro i
    rw [← InfiniteGalois.fixedField_fixingSubgroup K, IntermediateField.mem_fixedField_iff]
    exact fun g hg => hfix g hg i
  have h0 := hind d (fun i => ⟨hdK i, hdN i⟩) hdsum j
  rw [hdj] at h0
  exact one_ne_zero h0

theorem apply_mem_Kur {l : ℕ} [Fact l.Prime] (g : GQ l) (y : Om l) (hy : y ∈ MaximalUnramifiedExtension l) :
    g y ∈ MaximalUnramifiedExtension l := by
  delta MaximalUnramifiedExtension at hy ⊢
  have hmap : (IntermediateField.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m, 0 < m ∧ ¬l ∣ m ∧ x ^ m = 1}).map
      (g : PadicAlgCl l →ₐ[ℚ_[l]] PadicAlgCl l) ≤
      IntermediateField.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m, 0 < m ∧ ¬l ∣ m ∧ x ^ m = 1} := by
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨z, ⟨m, hm, hl, hz⟩, rfl⟩
    exact ⟨m, hm, hl, by rw [← map_pow, hz, map_one]⟩
  exact hmap ⟨y, hy, rfl⟩

theorem linearIndependent_Kur (l : ℕ) [Fact l.Prime] (K : FinExt l) (m : ℕ) (x : Fin m → ↥K.1)
    (hx : LinearIndependent ↥(K0 K) x) :
    LinearIndependent ↥(MaximalUnramifiedExtension l) (fun i => (x i : Om l)) := by
  rw [Fintype.linearIndependent_iff] at hx ⊢
  intro a ha
  have hcoe : ∀ z : ↥(K0 K), ((algebraMap ↥(K0 K) ↥K.1 z : ↥K.1) : Om l) = z := fun z => rfl
  have hzero := coeff_eq_zero_of_stable (F := ℚ_[l]) K.1 (MaximalUnramifiedExtension l) (fun g y hy => apply_mem_Kur g y hy)
    (fun i => (x i : Om l)) (fun i => (x i).2)
    (fun c hc hsum => by
      have hc0 := hx (fun i => ⟨c i, hc i⟩) (by
        apply Subtype.ext
        simpa [Algebra.smul_def, hcoe] using hsum)
      intro i
      simpa using congrArg Subtype.val (hc0 i))
    (fun i => (a i : Om l)) (fun i => (a i).2)
    (by simpa [Algebra.smul_def] using ha)
  intro i
  exact Subtype.ext (hzero i)

end GlobalTheory.UnramDisjoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CohomologyShapeOfTateDualityEulerStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_shape_of_tate_duality_euler : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ReciprocityTheory.ChartRestriction.T2.ShapeG := by
  first | exact @GlobalTheory.ShapeNeg.shapeG_of_localDuality | exact GlobalTheory.ShapeNeg.shapeG_of_localDuality | (intros; apply GlobalTheory.ShapeNeg.shapeG_of_localDuality <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHomModuloUnramifiedShapeOfLocalDualityStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisHom_modulo_unramified_shape_of_localDuality : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ReciprocityTheory.ChartRestriction.T2.ShapeUnr := by
  first | exact @GlobalTheory.ShapeUnrTriv.shapeUnr_of_localDuality | exact GlobalTheory.ShapeUnrTriv.shapeUnr_of_localDuality | (intros; apply GlobalTheory.ShapeUnrTriv.shapeUnr_of_localDuality <;> assumption)
end

