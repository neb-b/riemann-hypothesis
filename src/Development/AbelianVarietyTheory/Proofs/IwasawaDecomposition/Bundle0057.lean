module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFiltrationApproxByEnvelopeKernelPower
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem dense_ker_of_bounded {A R C Q : Type} [CommRing A] [CommRing R] [CommRing C] [CommRing Q]
    (p : ℕ) (α : A →+* R) (i : R →+* C) (f : C →+* Q) (N : ℕ)
    (hd : ∀ (x : C) (r : ℕ), ∃ (s : R) (z : C), x = i s + (p : C) ^ r * z)
    (hb : ∀ x : C, ∃ a : A, (p : Q) ^ N * f x = f (i (α a)))
    (x : C) (hx : f x = 0) :
    ∃ (u : R) (z : C), f (i u) = 0 ∧ x = i u + (p : C) * z := by
  obtain ⟨s, z, rfl⟩ := hd x (N + 1)
  obtain ⟨a, ha⟩ := hb z
  refine ⟨s + (p : R) * α a, (p : C) ^ N * z - i (α a), ?_, ?_⟩
  · rw [map_add (f := _), map_mul, map_pow, map_natCast] at hx
    rw [map_add (f := _), map_mul, map_natCast, map_add (f := _), map_mul, map_natCast, ← ha, ← hx]
    ring
  · rw [map_add (f := _), map_mul, map_natCast]
    ring

theorem ev_algebraMap (l : ℕ) [Fact l.Prime] (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  GlobalTheory.RingIface.ev_alg l n a

theorem fil_dense : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → ∀ (n : ℕ) (x : Per.Acris l), j x ∈ Per.FilP l n → ∃ (u : Per.Acris0 l) (z : Per.Acris l), (u : Per.AinfP l) ∈ Per.kerP l ^ n ∧ x = algebraMap (Per.Acris0 l) (Per.Acris l) u + (l : Per.Acris l) * z := by
  intro l _ j hj n x hx
  obtain ⟨N, hN⟩ := hj.bdd n
  have h0 : ∀ u : Per.Acris0 l, ((Per.ev l n).comp j) (algebraMap (Per.Acris0 l) (Per.Acris l) u) =
      Ideal.Quotient.mk _ (u : Per.AinfP l) := fun u => by
    rw [RingHom.comp_apply, hj.on0, ev_algebraMap]
  obtain ⟨u, z, hu, hz⟩ := dense_ker_of_bounded l (algebraMap (Per.Ainf l) (Per.Acris0 l))
    (algebraMap (Per.Acris0 l) (Per.Acris l)) ((Per.ev l n).comp j) N (acris_basic l).2.2.1
    (fun y => by
      obtain ⟨a, ha⟩ := hN y
      refine ⟨a, ?_⟩
      rw [map_mul, map_pow, map_natCast] at ha
      rw [h0]
      exact ha) x ((GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l n (j x)).1 hx)
  refine ⟨u, z, ?_, hz⟩
  rw [h0] at hu
  exact Ideal.Quotient.eq_zero_iff_mem.1 hu

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisMembershipSpanIff
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem adjoin_dividedPowers_iff_span {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : A)) (ξ : R) (P : R → Prop) (hP : ∀ a, P a ↔ ξ ∣ a) (s : A) :
    s ∈ Algebra.adjoin R {y : A | ∃ x : R, P x ∧ ∃ n : ℕ, ((n.factorial : ℕ) : A) * y = algebraMap R A x ^ n} ↔
      s ∈ Submodule.span R {y : A | ∃ n : ℕ, ((n.factorial : ℕ) : A) * y = algebraMap R A ξ ^ n} := by
  set S : Set A := {y : A | ∃ n : ℕ, ((n.factorial : ℕ) : A) * y = algebraMap R A ξ ^ n} with hS
  have hγ : ∀ n : ℕ, ∃ g : A, ((n.factorial : ℕ) : A) * g = algebraMap R A ξ ^ n := fun n => by
    obtain ⟨u, hu'⟩ := (hu n).exists_right_inv
    exact ⟨u * algebraMap R A ξ ^ n, by rw [← mul_assoc, hu', one_mul]⟩
  have hone : (1 : A) ∈ Submodule.span R S := Submodule.subset_span ⟨0, by simp⟩
  have hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ Submodule.span R S := by
    rintro x ⟨m, hm⟩ y ⟨n, hn⟩
    obtain ⟨g, hg⟩ := hγ (m + n)
    have hf : (((m + n).factorial : ℕ) : A) =
        (((m + n).choose n : ℕ) : A) * (m.factorial : ℕ) * (n.factorial : ℕ) := by
      rw [← Nat.add_choose_mul_factorial_mul_factorial m n]; push_cast; ring
    have : x * y = ((m + n).choose n : R) • g := by
      refine ((hu m).mul (hu n)).mul_left_cancel ?_
      rw [Algebra.smul_def, map_natCast]
      rw [hf, pow_add, ← hm, ← hn] at hg
      linear_combination -hg
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m + n, hg⟩)
  constructor
  · intro hs
    induction hs using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨x, hx, n, hn⟩ := hy
      obtain ⟨a, rfl⟩ := (hP x).1 hx
      obtain ⟨g, hg⟩ := hγ n
      have : y = (a ^ n) • g := by
        refine (hu n).mul_left_cancel ?_
        rw [hn, Algebra.smul_def, map_mul, mul_pow, ← hg, map_pow]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, hg⟩)
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ hone
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      have := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      refine Submodule.span_le.2 ?_ this
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact hmul a ha b hb
  · intro hs
    refine (Submodule.span_le (p := Subalgebra.toSubmodule (Algebra.adjoin R _))).2 ?_ hs
    rintro y ⟨n, hn⟩
    exact Algebra.subset_adjoin ⟨ξ, (hP ξ).2 dvd_rfl, n, hn⟩

theorem mem_Acris0_iff_span : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ s : Per.AinfP l,
    s ∈ Per.Acris0 l ↔ s ∈ Submodule.span (Per.Ainf l) {y : Per.AinfP l | ∃ n : ℕ,
      ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n} := by
  intro l _ e he s
  refine Iff.trans ?_ (adjoin_dividedPowers_iff_span (fun n => GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero) (xi e)
    (fun a => Per.θ l a = 0) (_root_.GlobalTheory.MemLoc.theta_eq_zero_iff_xi_dvd l e he) s)
  constructor
  · intro hs
    refine (?_ : Per.Acris0 l ≤ _) hs
    refine GlobalTheory.RingIface.Acris0_le_of_dividedPowers l _ fun x n y hx hy => ?_
    exact Algebra.subset_adjoin ⟨x, hx, n, hy⟩
  · intro hs
    refine Algebra.adjoin_le (S := Per.Acris0 l) ?_ hs
    rintro y ⟨x, hx, n, hy⟩
    exact GlobalTheory.RingIface.dividedPower_mem_Acris0 l x n y hx hy

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AxSenTateComplexPadicFixedClosure
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem ax_sen_tate : ∀ (l : ℕ) [Fact l.Prime], ∀ (H : Subgroup (GQ l)) (x : ℂ_[l]),
    (∀ g ∈ H, Per.σC g x = x) →
      x ∈ closure ((fun y : Om l => (y : ℂ_[l])) '' {y | ∀ g ∈ H, g y = y}) := by
  intro l _ H x hx
  obtain ⟨c, hc, hax⟩ := _root_.GlobalTheory.AxLemma.ax_lemma l
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hd : DenseRange (fun y : Om l => (y : ℂ_[l])) := by
    intro z
    induction z using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_closure
    | ih a => exact subset_closure ⟨a, rfl⟩
  have hδ : 0 < ε / (2 * c + 2) := by positivity
  obtain ⟨a, ha⟩ := hd.exists_dist_lt x hδ
  set δ := ε / (2 * c + 2) with hδdef
  have hmul : δ * (2 * c + 2) = ε := by
    rw [hδdef]; field_simp
  rw [dist_eq_norm] at ha
  have hsub : ∀ u v : Om l, ‖u - v‖ = ‖(u : ℂ_[l]) - (v : ℂ_[l])‖ := by
    intro u v
    rw [← PadicComplex.norm_extends, PadicComplex.coe_eq, PadicComplex.coe_eq,
      PadicComplex.coe_eq, map_sub]
  obtain ⟨y, hy, hxy⟩ := hax H a (2 * δ) (by
    intro g hg
    have h1 : ((g a : Om l) : ℂ_[l]) - (a : ℂ_[l])
        = (x - (a : ℂ_[l])) - Per.σC g (x - (a : ℂ_[l])) := by
      rw [map_sub, hx g hg, GlobalTheory.RingBasics.σC_coe]; ring
    rw [hsub, h1]
    have h2 := norm_sub_le (x - (a : ℂ_[l])) (Per.σC g (x - (a : ℂ_[l])))
    rw [GlobalTheory.RingBasics.norm_σC] at h2
    linarith)
  refine ⟨(y : ℂ_[l]), ⟨y, hy, rfl⟩, ?_⟩
  rw [hsub] at hxy
  have h3 := norm_add_le (x - (a : ℂ_[l])) ((a : ℂ_[l]) - (y : ℂ_[l]))
  rw [sub_add_sub_cancel] at h3
  rw [dist_eq_norm]
  nlinarith

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusSimpleRootsSectionUniqueEquivariant
section
noncomputable section
namespace GlobalTheory.MemLoc.SecUniq
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem root_eq {K R C : Type} [Field K] [CommRing R] [Field C] (θ : R →+* C)
    (hu : ∀ y : R, θ y ≠ 0 → IsUnit y) (o : K →+* R) (x : K) (y : R) (f : Polynomial K)
    (hy : θ y = θ (o x)) (h0 : f.eval x = 0) (h1 : f.derivative.eval x ≠ 0)
    (h2 : (f.map o).eval y = 0) : y = o x := by
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (f.map o) (o x) (y - o x)
  rw [add_sub_cancel, h2, Polynomial.derivative_map, Polynomial.eval_map_apply,
    Polynomial.eval_map_apply, h0, map_zero, zero_add] at hk
  have hθ : θ (y - o x) = 0 := by rw [map_sub, hy, sub_self]
  have hun : IsUnit (o (f.derivative.eval x) + k * (y - o x)) := by
    apply hu
    rw [map_add (f := _), map_mul, hθ, mul_zero, add_zero]
    exact (map_ne_zero (θ.comp o)).2 h1
  have : (o (f.derivative.eval x) + k * (y - o x)) * (y - o x) = 0 := by
    rw [hk]; ring
  exact sub_eq_zero.1 ((hun.mul_right_eq_zero).1 this)

variable {l : ℕ} [Fact l.Prime]

theorem padicInt_hom_ext_pt {R : Type} [CommRing R] [IsHausdorff (Ideal.span {((l : ℕ) : R)}) R]
    (f g : ℤ_[l] →+* R) (z : ℤ_[l]) : f z = g z := by
  refine sub_eq_zero.1 (IsHausdorff.haus (I := Ideal.span {((l : ℕ) : R)}) inferInstance _ fun n => ?_)
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n z)
  have hz : z = (PadicInt.appr z n : ℤ_[l]) + (l : ℤ_[l]) ^ n * w := by rw [← hw]; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨f w - g w, ?_⟩
  have h1 := congrArg f hz
  have h2 := congrArg g hz
  rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast] at h1 h2
  rw [h1, h2]
  ring

theorem sigA_zA (g : Per.Gq l) (z : ℤ_[l]) : Per.σA g (Per.zA l z) = Per.zA l z := by
  haveI : IsAdicComplete (Ideal.span {((l : ℕ) : Per.Ainf l)}) (Per.Ainf l) :=
    WittVector.isAdicCompleteIdealSpanP
  exact padicInt_hom_ext_pt ((Per.σA g).comp (Per.zA l)) (Per.zA l) z

theorem sigDp_aDp (g : Per.Gq l) (a : Per.Ainf l) : Per.σDp g (aDp l a) = aDp l (Per.σA g a) := by
  simp only [aDp, RingHom.comp_apply]
  rw [GlobalTheory.RingIface.sigDp_alg, GlobalTheory.RingBasics.awayMap_algebraMap₂]

theorem sec_root (o : Om l →+* Per.BdRp l) (ho : IsSec o) (x : Om l) (y : Per.BdRp l)
    (f : Polynomial (Om l)) (hy : Per.θD l y = (x : ℂ_[l])) (h0 : f.eval x = 0)
    (h1 : f.derivative.eval x ≠ 0) (h2 : (f.map o).eval y = 0) : y = o x :=
  root_eq (Per.θD l) (_root_.GlobalTheory.MemLoc.thetaD_props l).2.2.1 o x y f (by rw [hy, ho.th]) h0 h1 h2

theorem sec_uniq (o : Om l →+* Per.BdRp l) (ho : IsSec o) (o' : Om l →+* Per.BdRp l) (ho' : IsSec o') :
    o' = o := by
  have hq : o'.comp (algebraMap ℚ_[l] (Om l)) = o.comp (algebraMap ℚ_[l] (Om l)) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext fun z => ?_)
    exact (ho'.z z).trans (ho.z z).symm
  refine RingHom.ext fun x => ?_
  have hs : IsSeparable ℚ_[l] x := Algebra.IsSeparable.isSeparable ℚ_[l] x
  refine sec_root o ho x (o' x) ((minpoly ℚ_[l] x).map (algebraMap ℚ_[l] (Om l))) (ho'.th x) ?_ ?_ ?_
  · rw [Polynomial.eval_map_algebraMap, minpoly.aeval]
  · rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap]
    exact Polynomial.Separable.aeval_derivative_ne_zero hs (minpoly.aeval _ _)
  · rw [Polynomial.map_map, ← hq, ← Polynomial.map_map, Polynomial.eval_map_apply,
      Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]

theorem sec_equiv (o : Om l →+* Per.BdRp l) (ho : IsSec o) (g : Per.Gq l) (x : Om l) :
    Per.σDp g (o x) = o (g x) := by
  have h : IsSec (((Per.σDp g).comp o).comp (g.symm : Om l →+* Om l)) := by
    constructor
    · intro x
      change Per.θD l (Per.σDp g (o (g.symm x))) = _
      rw [(_root_.GlobalTheory.MemLoc.thetaD_props l).2.2.2.2, ho.th, GlobalTheory.RingBasics.σC_coe, AlgEquiv.apply_symm_apply]
    · intro z
      change Per.σDp g (o (g.symm (algebraMap ℚ_[l] (Om l) (z : ℚ_[l])))) = _
      rw [AlgEquiv.commutes, ho.z, sigDp_aDp, sigA_zA]
  have := RingHom.congr_fun (sec_uniq o ho _ h) (g x)
  rw [← this]
  change _ = Per.σDp g (o (g.symm (g x)))
  rw [AlgEquiv.symm_apply_apply]

theorem main : ∀ (l : ℕ) [Fact l.Prime], ∀ o : Om l →+* Per.BdRp l, IsSec o → (∀ (x : Om l) (y : Per.BdRp l) (f : Polynomial (Om l)), Per.θD l y = (x : ℂ_[l]) → f.eval x = 0 → f.derivative.eval x ≠ 0 → (f.map o).eval y = 0 → y = o x) ∧ (∀ o' : Om l →+* Per.BdRp l, IsSec o' → o' = o) ∧ ∀ (g : Per.Gq l) (x : Om l), Per.σDp g (o x) = o (g x) :=
  fun _ _ o ho => ⟨sec_root o ho, sec_uniq o ho, sec_equiv o ho⟩

end GlobalTheory.MemLoc.SecUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMatExp
section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

noncomputable section

namespace GlobalTheory.UpqExpChart

section General

variable {n : Type} [Fintype n] [DecidableEq n]

theorem continuous_matExp : Continuous (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.exp_continuous

theorem exists_chart : ∃ e : OpenPartialHomeomorph (Matrix n n ℂ) (Matrix n n ℂ),
    (e : Matrix n n ℂ → Matrix n n ℂ) = NormedSpace.exp ∧ (0 : Matrix n n ℂ) ∈ e.source := by
  open scoped Matrix.Norms.Operator in
  have h : HasStrictFDerivAt (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix n n ℂ) : Matrix n n ℂ ≃L[ℂ] Matrix n n ℂ) :
        Matrix n n ℂ →L[ℂ] Matrix n n ℂ) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Matrix n n ℂ)
  open scoped Matrix.Norms.Operator in
  exact ⟨h.toOpenPartialHomeomorph _, rfl, h.mem_toOpenPartialHomeomorph_source⟩

theorem exp_mul_exp_neg (X : Matrix n n ℂ) : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
  rw [← Matrix.exp_add_of_commute X (-X) (Commute.refl X).neg_right, add_neg_cancel,
    NormedSpace.exp_zero]

theorem exp_neg_mul_exp (X : Matrix n n ℂ) : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
  simpa using exp_mul_exp_neg (-X)

theorem exp_conj_invol {J : Matrix n n ℂ} (hJ : J * J = 1) (X : Matrix n n ℂ) :
    NormedSpace.exp (J * X * J) = J * NormedSpace.exp X * J :=
  Matrix.exp_units_conj (⟨J, J, hJ, hJ⟩ : (Matrix n n ℂ)ˣ) X

theorem exp_unitary {J : Matrix n n ℂ} (hJ : J * J = 1) {X : Matrix n n ℂ}
    (hX : Xᴴ * J + J * X = 0) : (NormedSpace.exp X)ᴴ * J * NormedSpace.exp X = J := by
  have h1 : Xᴴ = J * (-X) * J := by
    have : Xᴴ * J = J * (-X) := by rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hX
    rw [← this, Matrix.mul_assoc, hJ, Matrix.mul_one]
  rw [← Matrix.exp_conjTranspose, h1, exp_conj_invol hJ, Matrix.mul_assoc _ J J, hJ,
    Matrix.mul_one, Matrix.mul_assoc, exp_neg_mul_exp, Matrix.mul_one]

theorem exp_twist {J : Matrix n n ℂ} (hJ : J * J = 1) {Z : Matrix n n ℂ}
    (hZ : (NormedSpace.exp Z)ᴴ * J * NormedSpace.exp Z = J) :
    NormedSpace.exp (J * (-Z)ᴴ * J) = NormedSpace.exp Z := by
  rw [exp_conj_invol hJ, Matrix.exp_conjTranspose]
  have h1 : (NormedSpace.exp (-Z))ᴴ * (NormedSpace.exp Z)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, exp_mul_exp_neg, Matrix.conjTranspose_one]
  have h2 : (NormedSpace.exp (-Z))ᴴ * J = J * NormedSpace.exp Z := by
    calc (NormedSpace.exp (-Z))ᴴ * J
        = (NormedSpace.exp (-Z))ᴴ * ((NormedSpace.exp Z)ᴴ * J * NormedSpace.exp Z) := by rw [hZ]
      _ = J * NormedSpace.exp Z := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, hJ, Matrix.one_mul]

end General

theorem jpq_sq (P Q : ℕ) : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem mat_unitary {P Q : ℕ} (g : UpqT P Q) :
    (UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat g = Formalism.UG.Jpq P Q := g.2

theorem continuous_mat {P Q : ℕ} : Continuous (UpqT.mat : UpqT P Q → _) :=
  Units.continuous_val.comp continuous_subtype_val

end GlobalTheory.UpqExpChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetBoundedConvergentPowerSeriesMatrixETwoPi
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open Filter Topology

theorem tendsto_tsum_coeff_mul_pow_zero (a : ℕ → ℂ) (q₀ : ℂ) (hq₀ : q₀ ≠ 0)
    (hs : Summable (fun m : ℕ => a m * q₀ ^ m)) :
    Tendsto (fun q : ℂ => ∑' m : ℕ, a m * q ^ m) (𝓝 0) (𝓝 (a 0)) := by
  have hlim : Tendsto (fun q : ℂ => ∑' m : ℕ, a m * q ^ m) (𝓝 0)
      (𝓝 (∑' m : ℕ, if m = 0 then a 0 else 0)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun m => ‖a m * q₀ ^ m‖) hs.norm ?_ ?_
    · intro m
      have hc : Continuous (fun q : ℂ => a m * q ^ m) := by fun_prop
      have h := hc.tendsto 0
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simpa using h
      · have h0 : a m * (0 : ℂ) ^ m = 0 := by simp [hm.ne']
        rw [h0] at h
        simpa [hm.ne'] using h
    · have hpos : 0 < ‖q₀‖ := norm_pos_iff.mpr hq₀
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hpos] with q hq m
      have hq' : ‖q‖ ≤ ‖q₀‖ := by
        have : ‖q‖ < ‖q₀‖ := by simpa using hq
        exact this.le
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      gcongr
  simpa using hlim

theorem det_bounded_eTwoPi : ∀ (g : ℕ) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)) (w₀ : ℂ),
    IsUnit A.det → (∀ i j, Summable (fun m : ℕ => PowerSeries.coeff m (A i j) * eTwoPi w₀ ^ m)) →
    ∃ T' C : ℝ, 0 < C ∧ ∀ w : ℂ, T' < w.im →
      C⁻¹ ≤ ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ∧
      ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ≤ C := by
  intro g A w₀ hdet hsum
  have hq₀ : eTwoPi w₀ ≠ 0 := Complex.exp_ne_zero _
  set d₀ : ℂ := (A.map (PowerSeries.constantCoeff (R := ℂ))).det with hd₀
  have hd₀eq : d₀ = PowerSeries.constantCoeff (R := ℂ) A.det := by
    rw [RingHom.map_det]
    rfl
  have hd₀ne : d₀ ≠ 0 := by
    rw [hd₀eq]
    exact (hdet.map (PowerSeries.constantCoeff (R := ℂ))).ne_zero
  have hmat : Tendsto
      (fun q : ℂ => (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * q ^ m :
        Matrix (Fin g) (Fin g) ℂ)) (𝓝 0) (𝓝 (A.map (PowerSeries.constantCoeff (R := ℂ)))) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
    have h := tendsto_tsum_coeff_mul_pow_zero (fun m => PowerSeries.coeff m (A i j))
      (eTwoPi w₀) hq₀ (hsum i j)
    simpa using h
  have hdetlim : Tendsto
      (fun q : ℂ => (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * q ^ m :
        Matrix (Fin g) (Fin g) ℂ).det) (𝓝 0) (𝓝 d₀) :=
    ((continuous_id.matrix_det).tendsto _).comp hmat
  have hdpos : 0 < ‖d₀‖ := norm_pos_iff.mpr hd₀ne
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hdetlim (‖d₀‖ / 2) (by positivity))
  refine ⟨-Real.log ε / (2 * Real.pi), 2 / ‖d₀‖ + 3 * ‖d₀‖ / 2 + 1, by positivity, ?_⟩
  intro w hw
  have hpi : 0 < 2 * Real.pi := by positivity
  have hnorm : ‖eTwoPi w‖ < ε := by
    have hn : ‖eTwoPi w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
      rw [eTwoPi, Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im]
    rw [hn, ← Real.lt_log_iff_exp_lt hε]
    rw [div_lt_iff₀ hpi] at hw
    linarith
  have hclose := hball (y := eTwoPi w) (by simpa using hnorm)
  rw [dist_eq_norm] at hclose
  set D : ℂ := (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m :
    Matrix (Fin g) (Fin g) ℂ).det with hD
  have hlow : ‖d₀‖ / 2 ≤ ‖D‖ := by
    have := norm_sub_norm_le d₀ D
    rw [norm_sub_rev] at this
    linarith
  have hup : ‖D‖ ≤ 3 * ‖d₀‖ / 2 := by
    have := norm_sub_norm_le D d₀
    linarith
  have h2 : 0 < 2 / ‖d₀‖ := by positivity
  constructor
  · refine le_trans ?_ hlow
    have hC : 2 / ‖d₀‖ ≤ 2 / ‖d₀‖ + 3 * ‖d₀‖ / 2 + 1 := by
      have : 0 ≤ 3 * ‖d₀‖ / 2 := by positivity
      linarith
    have := inv_anti₀ h2 hC
    rwa [inv_div] at this
  · have : 0 < 2 / ‖d₀‖ := h2
    linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadicStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic : ∀ (l : ℕ) [Fact l.Prime], ∃ (ζ : ℕ → Om l) (ε : Per.Fl l), ζ 0 = 1 ∧ (∀ m, ζ (m + 1) ^ l = ζ m) ∧ ζ 1 ≠ 1 ∧ ∀ m, (rootT ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ζ m) := by
  first | exact @GlobalTheory.MemLoc.exists_zeta_eps | exact GlobalTheory.MemLoc.exists_zeta_eps | (intros; apply GlobalTheory.MemLoc.exists_zeta_eps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitPowNormVSubOneStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_pow_normV_sub_one' : ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (y : (v.adicCompletion E)ˣ),
    Valued.v ((y : v.adicCompletion E) - 1) < 1 →
    ∃ z : (v.adicCompletion E)ˣ, Valued.v (z : v.adicCompletion E) = 1 ∧ z ^ (normV v - 1) = y := by
  first | exact @GlobalTheory.OneUnitRoot.exists_unit_pow_normV_sub_one | exact GlobalTheory.OneUnitRoot.exists_unit_pow_normV_sub_one | (intros; apply GlobalTheory.OneUnitRoot.exists_unit_pow_normV_sub_one <;> assumption)
end

