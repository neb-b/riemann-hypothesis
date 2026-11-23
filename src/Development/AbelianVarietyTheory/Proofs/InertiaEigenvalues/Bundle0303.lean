module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicProductExtendedByZeroAssoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0125
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0220

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1LatticeRankGrowth
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

set_option autoImplicit false

namespace GlobalTheory.H1Rank

theorem growth_H1T_dim_H1V : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), Module.Finite O (LatticeCohomology LA) → Module.Finite LL (H1V A.ρ) ∧ ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) ≤ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ∧ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ C * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) := by
  intro l _ K LL _ _ _ O _ _ hG A LA hfin
  have hG' := hG
  obtain ⟨⟨hD, hDVR, hFr⟩, -, -, -, -⟩ := hG'
  haveI := hD
  haveI := hDVR
  haveI := hFr
  have hl0 : ((l : ℕ) : O) ≠ 0 := by
    intro h
    have h1 : algebraMap O LL ((l : ℕ) : O) = 0 := by rw [h, map_zero]
    rw [map_natCast] at h1
    have h2 : ((l : ℕ) : LL) = algebraMap ℚ_[l] LL (l : ℚ_[l]) := by rw [map_natCast]
    rw [h2] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) ((map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective).1 h1)
  have hfq : ∀ r : ℕ, Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ r}) :=
    (GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG).2.2.1
  have hfq1 : Finite (O ⧸ Ideal.span {((l : ℕ) : O)}) := by simpa using hfq 1
  have hsurj : ∀ y : H1V A.ρ, ∃ n : ℕ, ∃ x : LatticeCohomology LA, toH1V LA x = ((l : ℕ) : O) ^ n • y := by
    intro y
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨n, hn⟩ := pow_smul_mem_Z1T l K LL O hG A LA c.1 c.2
    refine ⟨n, Submodule.Quotient.mk ⟨_, hn⟩, ?_⟩
    rw [toH1V_mk]
    rfl
  have hker : ∀ x : LatticeCohomology LA, toH1V LA x = 0 → ∃ n : ℕ, ((l : ℕ) : O) ^ n • x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [toH1V_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨n, hn⟩ := pow_smul_mem_B1T l K LL O hG A LA c.1 c.2 hx
    refine ⟨n, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hn
  obtain ⟨hF, hr⟩ := finite_finrank_of_localizes O LL (LatticeCohomology LA) (H1V A.ρ) (toH1V LA) _ hl0 hsurj hker
  refine ⟨hF, ?_⟩
  rw [hr]
  obtain ⟨C, hC, hb⟩ := _root_.GlobalTheory.DVRQuotCount.card_quot_pow_smul_bounds O (LatticeCohomology LA) _ hl0 (not_isUnit_l l LL O hG) hfq
  have e2 : ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank O (LatticeCohomology LA)) = Nat.card (O ⧸ Ideal.span {((l : ℕ) : O) ^ r}) ^ finrank O (LatticeCohomology LA) := by
    intro r
    rw [_root_.GlobalTheory.card_quot_span_pow O _ hl0 hfq1 r, pow_mul]
  refine ⟨C, hC, fun r => ⟨?_, ?_⟩⟩
  · exact (e2 r).trans_le (hb r).1
  · exact (hb r).2.trans_eq (congrArg (C * ·) (e2 r).symm)

end GlobalTheory.H1Rank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionExteriorProductAssocComm
section
noncomputable section

namespace GlobalTheory.GLq.HcRing

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem toG_val {n : ℕ} (x : Gn g n) : toG (x : Mt g n) = x := by
  unfold toG
  rw [dif_pos x.isUnit]
  exact Units.ext rfl

theorem br_zero {a : ℕ} (M : Mt g a) : br 0 a M = M := by
  funext i j
  simp only [br, entN, zero_add, i.isLt, j.isLt, and_self, dif_pos]

theorem tl_self {a : ℕ} (M : Mt g a) : tl a M = M := by
  funext i j
  simp only [tl, entN, i.isLt, j.isLt, and_self, dif_pos]

theorem inPar_zero {n : ℕ} (M : Mt g n) : InPar 0 M := fun _ _ hj _ => absurd hj (Nat.not_lt_zero _)

theorem inPar_self {a : ℕ} (M : Mt g a) : InPar a M := fun i _ _ hi => absurd i.isLt (not_lt.2 hi)

theorem class_conj {G : Type} [Group G] {χ : G → ℂ} (h : IsClass χ) (x y : G) : χ (y⁻¹ * x * y) = χ x := by
  have := h x y⁻¹
  rwa [inv_inv] at this

theorem mean_class {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (h : IsClass χ) (x : G) :
    (Fintype.card G : ℂ)⁻¹ * ∑ y : G, χ (y⁻¹ * x * y) = χ x := by
  simp only [class_conj h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

theorem hc_one_left (a : ℕ) (α : Gn g a → ℂ) (hα : IsClass α) : hc 0 a (fun _ => 1) α a = α := by
  funext x
  unfold hc hcT
  simp only [inPar_zero, if_true, one_mul,
    br_zero, toG_val]
  rw [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.card_univ]
  exact mean_class hα x

theorem hc_one_right (a : ℕ) (α : Gn g a → ℂ) (hα : IsClass α) : hc a 0 α (fun _ => 1) a = α := by
  funext x
  unfold hc hcT
  simp only [inPar_self, if_true, mul_one,
    tl_self, toG_val]
  rw [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.card_univ]
  exact mean_class hα x

theorem main : ∀ (g : ℕ) [Fact g.Prime] (a b c n : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (γ : Gn g c → ℂ),
    IsClass α → IsClass β → IsClass γ →
      (n = a + b + c → hc (a + b) c (hc a b α β (a + b)) γ n = hc a (b + c) α (hc b c β γ (b + c)) n) ∧
      (n = a + b → hc a b α β n = hc b a β α n) ∧
      (hc 0 a (fun _ => 1) α a = α ∧ hc a 0 α (fun _ => 1) a = α) :=
  fun g _ a b c n α β γ hα hβ hγ =>
    ⟨GlobalTheory.GLm.HcAssoc.hc_assoc g a b c n α β γ hα hβ hγ, GlobalTheory.HCComm.main g a b n α β hα hβ,
      hc_one_left a α hα, hc_one_right a α hα⟩

end GlobalTheory.GLq.HcRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HighPowCoeffMemSpanPow
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.WittHighPow

theorem high_pow_coeff_mem_span_pow :
    ∀ {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p] (x : WittVector p R) (N m : ℕ), ∃ k : ℕ, ∀ (z : WittVector p R) (n : ℕ), n < N → (x ^ k * z).coeff n ∈ Ideal.span {x.coeff 0 ^ m} := by
  intro p _ R _ _ _ x N m
  classical
  set J : Ideal R := Ideal.span {x.coeff 0 ^ m} with hJ
  let f : WittVector p R →+* TruncatedWittVector p N (R ⧸ J) :=
    (WittVector.truncate N).comp (WittVector.map (Ideal.Quotient.mk J))
  have hmem : ∀ w : WittVector p R, w ∈ RingHom.ker f ↔ ∀ n < N, w.coeff n ∈ J := by
    intro w
    rw [RingHom.mem_ker]
    constructor
    · intro h n hn
      have := congrArg (fun t => TruncatedWittVector.coeff ⟨n, hn⟩ t) h
      simp only [f, RingHom.comp_apply, WittVector.coeff_truncate,
        WittVector.map_coeff, TruncatedWittVector.coeff_zero] at this
      exact (Ideal.Quotient.eq_zero_iff_mem).1 this
    · intro h
      ext i
      simp only [f, RingHom.comp_apply, WittVector.coeff_truncate,
        WittVector.map_coeff, TruncatedWittVector.coeff_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem).2 (h i i.2)
  set I := RingHom.ker f
  set ϖ := x.coeff 0
  set t : WittVector p R := WittVector.teichmuller p ϖ
  set y : WittVector p R := x - t
  have hy0 : y.coeff 0 = 0 := by
    have h1 : x = y + t := by simp [y]
    have h2 := congrArg (fun w => w.coeff 0) h1
    simp only [WittVector.add_coeff_zero, t, WittVector.teichmuller_coeff_zero] at h2
    linear_combination -h2
  have hyV : y = WittVector.verschiebung (y.shift 1) := by
    have := WittVector.eq_iterate_verschiebung (x := y) (n := 1) (by
      intro i hi; interval_cases i; exact hy0)
    simpa using this
  let u : WittVector p R := WittVector.mk p (fun n => (frobeniusEquiv R p).symm ((y.shift 1).coeff n))
  have hu : WittVector.frobenius u = y.shift 1 := by
    ext n
    rw [WittVector.coeff_frobenius_charP]
    simp only [u, WittVector.coeff_mk]
    exact frobenius_apply_frobeniusEquiv_symm R p _
  have hyp : y = u * (p : WittVector p R) := by
    rw [hyV, ← hu, WittVector.verschiebung_frobenius]
  have hx : x = t + u * (p : WittVector p R) := by
    rw [← hyp]; simp [y]
  have ht : t ^ m ∈ I := by
    rw [hmem]
    intro n _
    have : t ^ m = WittVector.teichmuller p (ϖ ^ m) := by simp [t, map_pow]
    rw [this]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rw [WittVector.teichmuller_coeff_zero]; exact Ideal.subset_span rfl
    · rw [WittVector.teichmuller_coeff_pos _ _ n h]; exact J.zero_mem
  have hp' : (u * (p : WittVector p R)) ^ N ∈ I := by
    rw [hmem]
    intro n hn
    rw [mul_pow, WittVector.mul_pow_charP_coeff_zero _ hn]
    exact J.zero_mem
  refine ⟨m + N, fun z n hn => ?_⟩
  have hk : x ^ (m + N) ∈ I := by
    rw [hx]; exact Ideal.add_pow_mem_of_pow_mem_of_le I ht hp' (by omega)
  exact (hmem _).1 (I.mul_mem_right z hk) n hn

end GlobalTheory.WittHighPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentImageStableOfEquivariant
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.EigRed

theorem mem_smul_of_sum_eigenvectors {O V ι α : Type*} [CommRing O] [AddCommGroup V] [Module O V]
    (I : Ideal O) (B : Submodule O V) (T : ι → Module.End O V) (hT : ∀ i, ∀ x ∈ B, T i x ∈ B) (ev : ι → O)
    (s : Finset α) :
    ∀ (y : α → V) (x : V), (∀ a ∈ s, y a = 0 ∨ ∃ e : ι → O, (∀ i, T i (y a) = e i • y a) ∧ ∃ i, IsUnit (ev i - e i)) →
      x = ∑ a ∈ s, y a → x ∈ B → (∀ i, T i x - ev i • x ∈ I • B) → x ∈ I • B := by
  classical
  have hTI : ∀ i, ∀ m ∈ I • B, T i m ∈ I • B := by
    intro i m hm
    refine Submodule.smul_induction_on hm (fun r hr n hn => ?_) (fun a b ha hb => ?_)
    · rw [map_smul]; exact Submodule.smul_mem_smul hr (hT i n hn)
    · rw [map_add]; exact add_mem ha hb
  induction s using Finset.induction_on with
  | empty => intro y x _ hx _ _; simp [hx]
  | insert a s ha ih =>
    intro y x hy hx hxB hev
    rw [Finset.sum_insert ha] at hx
    rcases hy a (Finset.mem_insert_self _ _) with h0 | ⟨e, he, i, hu⟩
    · exact ih y x (fun b hb => hy b (Finset.mem_insert_of_mem hb)) (by simpa [h0] using hx) hxB hev
    · have h1 : T i x - e i • x ∈ I • B := by
        refine ih (fun b => T i (y b) - e i • y b) _ (fun b hb => ?_) ?_ (sub_mem (hT i x hxB) (B.smul_mem _ hxB))
          (fun j => ?_)
        · rcases hy b (Finset.mem_insert_of_mem hb) with h0 | ⟨e', he', hu'⟩
          · left; simp [h0]
          · right
            refine ⟨e', fun j => ?_, hu'⟩
            rw [he' i, ← sub_smul, map_smul, he' j, smul_comm]
        set_option synthInstance.maxHeartbeats 100000 in
          · rw [hx, map_add (f := _), smul_add, he i, map_sum, Finset.smul_sum, Finset.sum_sub_distrib]; abel
        · have h2 : T j (T i x - e i • x) - ev j • (T i x - e i • x) =
              (ev i - e i) • (T j x - ev j • x) + (T j (T i x - ev i • x) - ev j • (T i x - ev i • x)) := by
            simp only [map_sub, map_smul]
            module
          rw [h2]
          exact add_mem (Submodule.smul_mem _ _ (hev j))
            (sub_mem (hTI j _ (hev i)) (Submodule.smul_mem _ _ (hev i)))
      have h3 : (ev i - e i) • x ∈ I • B := by
        have : (ev i - e i) • x = (T i x - e i • x) - (T i x - ev i • x) := by module
        rw [this]; exact sub_mem h1 (hev i)
      obtain ⟨u, hu⟩ := hu
      have h4 := Submodule.smul_mem _ ((u⁻¹ : Oˣ) : O) h3
      rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h4

open Formalism.MainNotions.IntegralHeckeForms

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem eG_idem (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) : eG Y i j b (eG Y i j b x) = eG Y i j b x := by
  rw [← mul_apply_eq_comp]
  unfold eG
  rw [← map_mul, Y.eAlg_idem]

theorem eG_comm (i : X.Tw) (j : ℕ) (b : Bool) (T : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (h : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ T = T ∘ₗ (Y.actG i j b g).toLinearMap) (x : Y.Fm i j b) :
    eG Y i j b (T x) = T (eG Y i j b x) := by
  unfold eG
  induction Y.eAlg i b using MonoidAlgebra.induction_on with
  | of g =>
    simp only [MonoidAlgebra.lift_of]
    exact LinearMap.congr_fun (h g) x
  | add f g hf hg => simp only [map_add (f := _), LinearMap.add_apply, hf, hg]
  | smul r f hf => simp only [map_smul, LinearMap.smul_apply, hf]

theorem idempotentImage_stable_of_equivariant (i : X.Tw) (j : ℕ) (b : Bool) (T : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (h : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ T = T ∘ₗ (Y.actG i j b g).toLinearMap) (x : Y.Fm i j b)
    (hx : x ∈ V0 Y i j b) : T x ∈ V0 Y i j b := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨T y, ?_, eG_comm Y i j b T h y⟩
  simp only [Fm0, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hy ⊢
  intro u
  have := LinearMap.congr_fun (h u) y
  simp only [LinearMap.comp_apply] at this
  rw [this, hy u, map_smul]

end GlobalTheory.EigRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCocyclesCharBlockOtherTypePrime
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.PolyInertia

theorem matKO_smul_one {O : Type} [CommRing O] [IsDomain O] {k : ℕ} (s : O) (z : KOG O k) :
    matKO (s • (1 : Matrix (Fin k) (Fin k) O)) z = s • z := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [← Submodule.Quotient.mk_smul]
  unfold matKO
  rw [Submodule.mapQ_apply]
  congr 1
  funext j
  simp [Matrix.mulVec, dotProduct, Algebra.smul_def, Matrix.algebraMap_matrix_apply]

theorem aeval_map_eq_sum {T O A : Type} [CommRing T] [CommRing O] [Ring A] [Algebra O A]
    (f : T →+* O) (P : Polynomial T) (a : A) :
    Polynomial.aeval a (P.map f) = ∑ k : Fin (P.natDegree + 1), f (P.coeff k) • a ^ (k : ℕ) := by
  rw [Polynomial.aeval_eq_sum_range' (n := P.natDegree + 1)
    (Nat.lt_succ_of_le Polynomial.natDegree_map_le), Finset.sum_range]
  simp only [Polynomial.coeff_map]

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ v ∈ D.nd.S i, PolyAt i r Xs π v → ∀ c : Fin D.R.t, resIne i (cocChi i r S Xs c) v = ⊥ := by
  intro D i r ρ π Xs S _ hG _ v hv hP c
  obtain ⟨P, hP0, hPu⟩ := hP
  obtain ⟨-, hdec, hψ, -, -, -, -, ⟨hT, -⟩, -, ⟨hπ, -⟩, -⟩ := hG
  set γ0 := D.nd.gam0 i v with hγ0
  let a : S.X' → MatN D.nd i := fun x' =>
    Polynomial.aeval (rO D.nd i r (S.p x') γ0) (P.map (evT D.nd i (S.p x')))
  have ha_eq : ∀ x', a x' = ∑ k : Fin (P.natDegree + 1),
      evT D.nd i (S.p x') (P.coeff k) • rO D.nd i r (S.p x') (γ0 ^ (k : ℕ)) := by
    intro x'
    simp only [a, aeval_map_eq_sum, map_pow]
  have ha : InR' D.nd r S a := by
    refine ⟨P.natDegree + 1, fun k x' => evT D.nd i (S.p x') (P.coeff k), fun k => γ0 ^ (k : ℕ),
      fun k => hT _ (P.coeff k).2, ?_⟩
    funext x'
    rw [ha_eq, Finset.sum_apply]
  have h1 : InR' D.nd r S 1 := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, ?_⟩
    funext x'
    simp
  have hchi : chiU D.nd i ((c : ℕ) + 1) γ0 = chiU D.nd i 1 γ0 :=
    (GlobalTheory.T.cyclotomicChar_unramified_away_from_ell D i v (D.nd.SQ_l i v (Or.inl hv)) γ0 (D.nd.locNd_chebotarevPlace_mem i v)).2 _
      (Nat.le_add_left _ _) c.2
  have hval : S.ψχ c a = (P.map (evT D.nd i π)).eval (D.nd.zeta i v) := by
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    let u := S.e.symm (0, Pi.single c 1)
    have hu : (S.e u).2 c = 1 := by simp [u]
    have e1 := congrArg (fun z => z.2 c) (hψ a ha u)
    simp only [hu, mul_one] at e1
    have e2 : ((a S.π').map (toK D.nd i)).mulVec u = ∑ k : Fin (P.natDegree + 1),
        toK D.nd i (evT D.nd i π (P.coeff k)) •
          (mapM (toK D.nd i) (rO D.nd i r π) (γ0 ^ (k : ℕ))).mulVec u := by
      rw [ha_eq, hπ]
      change ((toK D.nd i).mapMatrix _).mulVec u = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Matrix.sum_mulVec]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Matrix.smul_mulVec]
      congr 1
      ext p q
      simp [mapM]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e2, map_sum, Prod.snd_sum, Finset.sum_apply] at e1
    change toK D.nd i _ = toK D.nd i _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e1, ← Polynomial.coe_aeval_eq_eval, aeval_map_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hdec]
    simp only [Prod.smul_snd, Pi.smul_apply, hu, mul_one, map_pow, hchi, smul_eq_mul, map_mul,
      Units.val_pow_eq_pow_val]
    rfl
  rw [resIne, cocChi, cocW, Submodule.map_span, Submodule.span_eq_bot]
  rintro _ ⟨_, ⟨φ, hφ, hφ0, rfl⟩, rfl⟩
  funext γ
  change φ (yg D.nd r S γ) = 0
  have hy : InY D.nd r S (yg D.nd r S γ) :=
    ⟨1, fun _ => 1, fun _ => γ, fun _ => h1, by simp⟩
  have hay : InY D.nd r S (a * yg D.nd r S γ) :=
    ⟨1, fun _ => a, fun _ => γ, fun _ => ha, by simp⟩
  have hz : φ (a * yg D.nd r S γ) = 0 := by
    refine hφ0 _ hay fun x' hx' => ?_
    have h := hP0 (S.p x') hx' γ γ.2
    have : yg D.nd r S γ x' = (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
        ((rO D.nd i r (S.p x') γ - ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : MatN D.nd i)) *
          Eel D.nd S x') := by
      rw [yg, sub_mul, smul_sub, smul_mul_assoc, one_mul, smul_smul, Units.inv_mul, one_smul]
    rw [Pi.mul_apply, this, mul_smul_comm, ← mul_assoc]
    simp only [a]
    rw [h, zero_mul, smul_zero]
  rw [hφ a ha _ hy, matKO_smul_one, hval] at hz
  exact hPu.smul_eq_zero.mp hz

end GlobalTheory.Cut.PolyInertia
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveTensorBcrisToBdR
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.LocTensorK

private theorem ιB_algebraMap_Kur {l : ℕ} [Fact l.Prime] (P : LocPrime l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.ιB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) := by
  have hint : IsIntegral ℚ_[l] (c : Om l) := Algebra.IsIntegral.isIntegral _
  obtain ⟨K, hc⟩ : ∃ K : FinExt l, (c : Om l) ∈ K0 K :=
    ⟨⟨IntermediateField.adjoin ℚ_[l] {(c : Om l)},
      IntermediateField.adjoin.finiteDimensional hint⟩,
      IntermediateField.mem_adjoin_simple_self ℚ_[l] (c : Om l), c.2⟩
  have h := (P.PD K).ι.commutes (⟨c, hc⟩ : ↥(K0 K))
  rw [P.PD_ι] at h
  exact h

private theorem indep_of_frac {k Ω B D : Type} [Field k] [Field Ω] [CommRing B] [CommRing D] [Algebra k Ω]
    [IsGalois k Ω] (hD : IsField D) (o : Ω →+* D) (ι : B →+* D) (hι : Function.Injective ι)
    (hk : ∀ c : k, ∃ a : B, ι a = o (algebraMap k Ω c))
    (hfrac : ∀ (a b : B) (x : Ω), b ≠ 0 → ι a = o x * ι b → x ∈ (algebraMap k Ω).range)
    (m : ℕ) (x : Fin m → Ω) (hx : LinearIndependent k x) (b : Fin m → B)
    (hb : ∑ i, o (x i) * ι (b i) = 0) : ∀ i, b i = 0 := by
  letI : Field D := hD.toField
  have hcl : ∀ y : D, y ∈ Subring.closure (Set.range ι) ↔ ∃ a, ι a = y := by
    intro y
    have : Subring.closure (Set.range ι) = ι.range := by
      rw [← RingHom.coe_range, Subring.closure_eq]
    rw [this]; rfl
  have key := _root_.GlobalTheory.GalDisj.galois_linearDisjoint k Ω D o (Subfield.closure (Set.range ι)) (by
    intro y
    constructor
    · intro hy
      obtain ⟨u, hu, v, hv, huv⟩ := Subfield.mem_closure_iff.1 hy
      obtain ⟨a, rfl⟩ := (hcl u).1 hu
      obtain ⟨c, rfl⟩ := (hcl v).1 hv
      by_cases hc : c = 0
      · subst hc
        rw [map_zero, div_zero] at huv
        have : y = 0 := o.injective (by rw [map_zero]; exact huv.symm)
        rw [this]; exact zero_mem _
      · have hc' : ι c ≠ 0 := fun h => hc (hι (by rw [h, map_zero]))
        refine hfrac a c y hc ?_
        rw [← huv, div_mul_cancel₀ _ hc']
    · rintro ⟨c, rfl⟩
      obtain ⟨a, ha⟩ := hk c
      exact Subfield.subset_closure ⟨a, ha⟩) m x hx (fun i => ι (b i))
    (fun i => Subfield.subset_closure ⟨b i, rfl⟩) hb
  intro i
  exact hι (by rw [map_zero]; exact key i)

private theorem tied_tensor_inj : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (m : ℕ) (x : Fin m → Om l), LinearIndependent ↥(MaximalUnramifiedExtension l) x → ∀ b : Fin m → P.R.B, ∑ i, algebraMap (Om l) P.R.BdR (x i) * P.ιB (b i) = 0 → ∀ i, b i = 0 := by
  intro l _ P AI T m x hx b hb
  obtain ⟨hD, -, hι, -⟩ := GlobalTheory.Per.TiedField.tied_field l P AI T
  haveI : IsGalois ℚ_[l] (Om l) := inferInstance
  haveI : IsGalois ↥(MaximalUnramifiedExtension l) (Om l) := inferInstance
  refine indep_of_frac (k := ↥(MaximalUnramifiedExtension l)) hD (algebraMap (Om l) P.R.BdR) (P.ιB : P.R.B →+* P.R.BdR) hι
    (fun c => ⟨algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c, ιB_algebraMap_Kur P c⟩) ?_ m x hx b hb
  intro a c y hc h
  exact ⟨⟨y, _root_.GlobalTheory.FracAlg.mem_Kur_of_ratio l P AI T a c y hc h⟩, rfl⟩

end GlobalTheory.LocTensorK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_tensor_Bcris_to_BdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (m : ℕ) (x : Fin m → ↥K.1), LinearIndependent ↥(K0 K) x → ∀ b : Fin m → P.R.B, ∑ i, algebraMap ↥K.1 P.R.BdR (x i) * P.ιB (b i) = 0 → ∀ i, b i = 0 := by
  intro l _ P AI hT K m x hx b hb
  refine GlobalTheory.LocTensorK.tied_tensor_inj l P AI hT m (fun i => (x i : Om l))
    (GlobalTheory.UnramDisjoint.linearIndependent_Kur l K m x hx) b ?_
  exact hb
end

