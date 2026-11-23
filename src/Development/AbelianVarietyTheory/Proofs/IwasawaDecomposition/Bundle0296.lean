module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDeco
section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Col2.ClsZero

section Canon
variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ : LevFam X.E X.K n SG)

def canon (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) :=
  Classical.epsilon (p := fun d' => ∃ (γ : UF X.E n) (k : Λ.grp),
    d' = ((γ, (k.1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d) (h := ⟨d⟩)

theorem canon_spec (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : ∃ (γ : UF X.E n) (k : Λ.grp),
    canon Λ d = ((γ, (k.1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d :=
  Classical.epsilon_spec (p := fun d' => ∃ (γ : UF X.E n) (k : Λ.grp), d' = ((γ, (k.1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d)
    ⟨d, 1, 1, (one_smul _ d).symm⟩

theorem canon_smul (γ : UF X.E n) (k : Λ.grp) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) :
    canon Λ (((γ, (k.1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d) = canon Λ d := by
  unfold canon
  congr 1
  funext d'
  apply propext
  constructor
  · rintro ⟨γ', k', rfl⟩
    exact ⟨γ' * γ, k' * k, by rw [← mul_smul]; rfl⟩
  · rintro ⟨γ', k', rfl⟩
    refine ⟨γ' * γ⁻¹, k' * k⁻¹, ?_⟩
    rw [← mul_smul]
    congr 1
    ext1 <;> simp

theorem canon_idem (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : canon Λ (canon Λ d) = canon Λ d := by
  obtain ⟨γ, k, h⟩ := canon_spec Λ d
  conv_lhs => rw [h]
  exact canon_smul Λ γ k d

theorem orb_iff (y : Ys X n) (Λ' : LevFam X.E X.K n SG) (hΛ : Λ' = Λ) (Θ : LevQFam X.E X.K n Q) (hΘ : Θ = LevQFam.top X.E X.K n Q)
    (hy : y = Ys.triv X n) (p p' : PtY ST SG Q y) :
    (letI := ptYAct (ST := ST) y Λ' Θ; ∃ g : FrmG Λ' Θ, g • p = p') ↔ canon Λ p'.1.1.deco = canon Λ p.1.1.deco := by
  subst hΛ hΘ hy
  constructor
  · rintro ⟨g, rfl⟩
    exact canon_smul Λ' g.1 g.2.1 p.1.1.deco
  · intro h
    obtain ⟨γ₁, k₁, h₁⟩ := canon_spec Λ' p.1.1.deco
    obtain ⟨γ₂, k₂, h₂⟩ := canon_spec Λ' p'.1.1.deco
    have e : p'.1.1.deco = (((γ₂⁻¹ * γ₁ : UF X.E n), ((k₂⁻¹ * k₁ : Λ'.grp).1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • p.1.1.deco := by
      have := h₂.symm.trans (h.trans h₁)
      rw [← eq_inv_smul_iff, ← mul_smul] at this
      exact this
    generalize γ₂⁻¹ * γ₁ = γ at e
    generalize k₂⁻¹ * k₁ = k at e
    let q : DecoF X.E n ST SG Q := ((γ, k.1, 1) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • p.1.1
    have hq : q.deco = p'.1.1.deco := e.symm
    have hc : ∀ P : Q, (p'.1.1.fr P)⁻¹ * q.fr P ∈ GLint X.E n P.1 := by
      intro P x
      have h1 := q.2 P x
      have h2 := p'.1.1.2 P ((p'.1.1.fr P)⁻¹ (q.fr P x))
      have h3 : p'.1.1.1.2 P ((p'.1.1.fr P)⁻¹ (q.fr P x)) = q.fr P x := LinearEquiv.apply_symm_apply _ _
      rw [h3] at h2
      have h4 : q.1.1 = p'.1.1.1.1 := hq
      rw [h4] at h1
      exact h2.symm.trans h1
    refine ⟨(γ, k, ⟨fun P => ⟨_, hc P⟩, fun _ _ => trivial⟩), ?_⟩
    refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext e.symm ?_)) ?_)
    · funext P
      show γ.1 * p.1.1.fr P * ((p'.1.1.fr P)⁻¹ * (γ.1 * p.1.1.fr P * ((1 : GLQ X.E n Q) P)⁻¹.1))⁻¹ = p'.1.1.fr P
      simp only [Pi.one_apply, inv_one, OneMemClass.coe_one, mul_one]
      group
    · have h1 : p.1.2 = ∅ := p.2
      have h2 : p'.1.2 = ∅ := p'.2
      show (fun v => γ.1 v) '' p.1.2 = p'.1.2
      rw [h1, h2, Set.image_empty]

theorem eps_eq (y : Ys X n) (Λ' : LevFam X.E X.K n SG) (hΛ : Λ' = Λ) (Θ : LevQFam X.E X.K n Q) (p : PtY ST SG Q y) :
    (letI := ptYAct (ST := ST) y Λ' Θ
     Classical.epsilon (p := fun r => ∃ g : FrmG Λ' Θ, r = (g • p).1.1.deco) (h := ⟨p.1.1.deco⟩)) = canon Λ p.1.1.deco := by
  subst hΛ
  unfold canon
  congr 1
  funext r
  apply propext
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.1, g.2.1, rfl⟩
  · rintro ⟨γ, k, rfl⟩
    exact ⟨(γ, k, 1), rfl⟩

end Canon

attribute [local instance] starE
variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem levelTypePrimes_stepZero_eq_colLev (h : I.Ok) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0) :
    levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b = colLev I.Ch 0 := by
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 (by have := B.R.two_le_m; omega)) (by simp)
  · exact (h.idx_ok a).zero_G b

theorem chartIndexLevelTwistPrimes_stepZero_eq_top (h : I.Ok) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0) :
    levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b = LevQFam.top _ _ _ _ := by
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 (by have := B.R.two_le_m; omega)) (by simp)
  · exact (h.idx_ok a).zero_Q b

theorem ys0 (a : I.ι) : ysAt B.R I.sel (I.tup a) (I.cst a) 0 = Ys.triv _ _ :=
  if_neg (by have := B.R.two_le_m; omega)

theorem stepZero_chartIndex_subsingleton (h : I.Ok) (a : I.ι) (b b' : Idx I.sel (I.tup a) (I.idx a) 0) : b = b' := by
  have hm : 0 < B.R.m := by have := B.R.two_le_m; omega
  obtain ⟨b0, hb0⟩ := (h.idx_ok a).zero_uniq
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 hm) (by simp)
  obtain ⟨_ | b', hb'⟩ := b'
  · exact absurd (hb'.2 hm) (by simp)
  obtain rfl : b = b' := (hb0 b).trans (hb0 b').symm
  rfl

theorem stepZero_chartIndex_nonempty (h : I.Ok) (a : I.ι) : Nonempty (Idx I.sel (I.tup a) (I.idx a) 0) := by
  obtain ⟨b0, -⟩ := (h.idx_ok a).zero_uniq
  exact ⟨⟨some b0, by have := B.R.two_le_m; simp; omega⟩⟩

theorem cl_eq_iff (h : I.Ok) (u : B.Word) (a : I.ι) (b b' : Idx I.sel (I.tup a) (I.idx a) 0) (p p' : PtAt B.R I.sel (I.tup a) (I.cst a) u 0) :
    (I.stp u a 0).cl b p = (I.stp u a 0).cl b' p' ↔ canon (colLev I.Ch 0) p.1.1.deco = canon (colLev I.Ch 0) p'.1.1.deco := by
  obtain rfl := stepZero_chartIndex_subsingleton h a b b'
  rw [← orb_iff (colLev I.Ch 0) _ _ (levelTypePrimes_stepZero_eq_colLev h a b) _ (chartIndexLevelTwistPrimes_stepZero_eq_top h a b) (ys0 a) p' p]
  constructor
  · intro e
    exact Quotient.exact (eq_of_heq (Sigma.mk.inj e).2)
  · intro e
    exact congrArg (Sigma.mk b) (Quotient.sound e)

theorem cl_rep {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (c : S.Cl) : S.cl c.1 (S.rep c) = c :=
  congrArg (Sigma.mk c.1) (S.rp_spec c.1 c.2)

theorem bij0 (h : I.Ok) (u : B.Word) (a : I.ι) (b) : Function.Bijective (I.cl0 u a b) := by
  constructor
  · intro c c' e
    have e1 := (cl_eq_iff h u a b b _ _).1 e
    rw [← cl_rep _ c, ← cl_rep _ c']
    exact (cl_eq_iff h u I.mu0 _ _ _ _).2 e1
  · intro c
    obtain ⟨b0⟩ := stepZero_chartIndex_nonempty h I.mu0
    refine ⟨(I.stp u I.mu0 0).cl b0 (I.pt0 u a I.mu0 ((I.stp u a 0).rep c)), ?_⟩
    have e := (cl_eq_iff h u I.mu0 _ _ _ _).1 (cl_rep _ ((I.stp u I.mu0 0).cl b0 (I.pt0 u a I.mu0 ((I.stp u a 0).rep c))))
    refine Eq.trans ?_ (cl_rep _ c)
    exact (cl_eq_iff h u a _ _ _ _).2 e

theorem stepZero_preferred_iff_canonicalRep (h : I.Ok) (u : B.Word) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0)
    (p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0) :
    I.pref u a 0 b p ↔ p.1.1.deco = canon (colLev I.Ch 0) p.1.1.deco := by
  have hm := B.R.two_le_m
  have e := eps_eq (ST := (B.primes X).vT u) (colLev I.Ch 0) _ _ (levelTypePrimes_stepZero_eq_colLev h a b)
    (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b) p
  constructor
  · intro hp
    exact Eq.trans (hp.1 rfl) e
  · intro hp
    exact ⟨fun _ => hp.trans e.symm, fun e' => absurd e' (by omega),
      topLev_pref_ne I.Ch I.sel (I.tup a) (I.cst a) I.Ps u (by omega) _⟩

theorem empty_mem_couplingIndexAtStep_zero (a : I.ι) (N) : ∅ ∈ (ysAt B.R I.sel (I.tup a) (I.cst a) 0).ys N := by
  rw [ys0]; rfl

theorem stepZero_representative_deco_eq_canonical (h : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) :
    ((I.stp u a 0).rep c).1.1.deco = canon (colLev I.Ch 0) ((I.stp u a 0).rep c).1.1.deco := by
  obtain ⟨b, q⟩ := c
  let p := (I.stp u a 0).rep ⟨b, q⟩
  obtain ⟨γ, k, e⟩ := canon_spec (colLev I.Ch 0) p.1.1.deco
  let p' : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 := ⟨(((γ, k.1, 1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N 0) (I.Q a)) • p.1.1, ∅), empty_mem_couplingIndexAtStep_zero a _⟩
  have e' : p'.1.1.deco = canon (colLev I.Ch 0) p.1.1.deco := e.symm
  have hc : (I.stp u a 0).cl b p' = ⟨b, q⟩ := by
    refine Eq.trans ?_ (cl_rep _ ⟨b, q⟩)
    refine (cl_eq_iff h u a b b _ _).2 ?_
    rw [e', canon_idem]
  have hp := @pref_prefRep _ _ _ ((I.stp0 u a 0).actD b) (I.pref u a 0 b) p'
    ((stepZero_preferred_iff_canonicalRep h u a b p').2 (by rw [e', canon_idem]))
  have hq : q = Quotient.mk _ p' := (eq_of_heq (Sigma.mk.inj hc).2).symm
  refine (stepZero_preferred_iff_canonicalRep h u a b _).1 ?_
  rw [hq]
  exact hp

theorem stepZero_corresponding_representatives_same_deco (h : I.Ok) (u : B.Word) (a : I.ι) (b) (c : (I.stp u I.mu0 0).Cl) :
    ((I.stp u a 0).rep (I.cl0 u a b c)).1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
  refine (stepZero_representative_deco_eq_canonical h u a _).trans (Eq.trans ?_ (stepZero_representative_deco_eq_canonical h u I.mu0 c).symm)
  exact (cl_eq_iff h u a (I.cl0 u a b c).1 b ((I.stp u a 0).rep (I.cl0 u a b c))
    (I.pt0 u I.mu0 a ((I.stp u I.mu0 0).rep c))).1 (cl_rep (I.stp u a 0) (I.cl0 u a b c))

theorem stepZero_classes_bijective_same_deco : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a b,
    Function.Bijective (I.cl0 u a b) ∧
      ∀ c, ((I.stp u a 0).rep (I.cl0 u a b c)).1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco :=
  fun _ h u a b => ⟨bij0 h u a b, stepZero_corresponding_representatives_same_deco h u a b⟩

end GlobalTheory.Mem.Col2.ClsZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffBlockSymbolDetPowCayley
section
set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.PGsh

namespace GlobalTheory.CayleyBlock

theorem det_pow_eq {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q) :
    (GlobalTheory.DomainDens.blockSym h1 ()).det ^ q = rename (blockEmb h1) (sumMap p q (cayDet p ℂ ^ q)) := by
  rw [map_pow, map_pow, cayDet, AlgHom.map_det, AlgHom.map_det]
  congr 2
  ext i j
  simp [GlobalTheory.DomainDens.blockSym_apply, sumMap, blockEmb, Matrix.mvPolynomialX]

theorem bigList_nodup {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : (bigList τ).Nodup := by
  rw [bigList, List.nodup_flatMap]
  refine ⟨fun b _ => (List.nodup_finRange p).map fun j k h => by simpa using congrArg (fun x => x.2.2) h, ?_⟩
  refine (List.nodup_finRange q).imp fun {a b} hab => ?_
  show List.Disjoint _ _
  rw [List.disjoint_left]
  intro x hx hy
  simp only [List.mem_map, List.mem_finRange, true_and] at hx hy
  obtain ⟨j, rfl⟩ := hx
  obtain ⟨k, hk⟩ := hy
  exact hab (congrArg Prod.fst hk).symm

theorem bigList_sum {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) :
    ((bigList τ).map fun v => Finsupp.single v 1).sum = blockGraph τ := by
  simp [bigList, blockGraph, List.map_flatMap, Fin.sum_univ_def, List.map_map, Function.comp_def]
  simp [List.flatMap, List.sum_flatten, List.map_map, Function.comp_def]

theorem pderiv_sumMap {p q : ℕ} (v : Fin q × Fin p × Fin p) (P : MvPolynomial (Fin p × Fin p) ℂ) :
    pderiv v (sumMap p q P) = sumMap p q (pderiv v.2 P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [sumMap]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]
  | mul_X f w hf =>
    simp only [map_mul, Derivation.leibniz, hf, smul_eq_mul, map_add (f := _)]
    congr 1
    simp [sumMap, pderiv_X, Pi.single_apply, Prod.ext_iff]
    by_cases h : w.1 = v.2.1 ∧ w.2 = v.2.2 <;> simp [h, Finset.filter_eq']

theorem dList_sumMap {p q : ℕ} (l : List (Fin q × Fin p × Fin p)) (P : MvPolynomial (Fin p × Fin p) ℂ) :
    dList l (sumMap p q P) = sumMap p q (dList (l.map fun v => v.2) P) := by
  induction l with
  | nil => simp [dList]
  | cons v l ih =>
    simp only [dList, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
    rw [ih]
    exact pderiv_sumMap v _

theorem bigList_map {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : (bigList τ).map (fun v => v.2) = smallList τ := by
  simp [bigList, smallList, List.map_flatMap, List.map_map, Function.comp_def]

theorem constantCoeff_sumMap (p q : ℕ) (P : MvPolynomial (Fin p × Fin p) ℂ) :
    constantCoeff (sumMap p q P) = constantCoeff P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [sumMap]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]
  | mul_X f w hf => simp [sumMap, constantCoeff_X]

end GlobalTheory.CayleyBlock


open GlobalTheory.CayleyBlock ReciprocityTheory.PGsh MvPolynomial in
theorem GlobalTheory.topCoeff_blockSym_det_pow : ∀ (p q : ℕ) (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q),
    GlobalTheory.GoodMetric.topCoeff ((GlobalTheory.DomainDens.blockSym h1 ()).det ^ q) =
      ∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial) := by
  intro p q h1
  rw [det_pow_eq, _root_.GlobalTheory.CayleyBlock.topCoeff_rename_blockEmb, ← _root_.GlobalTheory.constantCoeff_cayOp_pow_cayDet_pow, _root_.GlobalTheory.CayleyBlock.cayOp_pow_eq_sum, LinearMap.sum_apply]
  have key : ∀ τ : Fin q → Equiv.Perm (Fin p), (sgnProd τ : ℂ) * AddMonoidAlgebra.coeff (sumMap p q (cayDet p ℂ ^ q)) (blockGraph τ) =
      constantCoeff (sgnProd τ • dList (smallList τ) (cayDet p ℂ ^ q)) := by
    intro τ
    rw [← bigList_sum, ← zero_add ((bigList τ).map _).sum, ← GlobalTheory.T.coeff_composedPartialDerivList_of_nodup _ (bigList_nodup τ) 0 (fun _ _ => rfl),
      dList_sumMap, bigList_map, ← constantCoeff_sumMap p q, map_zsmul, zsmul_eq_mul,
      ← map_intCast (C : ℂ →+* MvPolynomial (Fin q × Fin p × Fin p) ℂ), map_mul, constantCoeff_C, constantCoeff_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [LinearMap.smul_apply, key, map_sum]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowEqSumSmulCoeffCharpolyRevPow
section
set_option autoImplicit false

noncomputable section

open Polynomial

namespace GlobalTheory

namespace LogTrace

theorem coeff_sub_one_pow {S : Type} [CommRing S] [Algebra ℝ S] (f : S[X]) (s n : ℕ) (hs : s ≤ n) :
    ((f - 1) ^ s).coeff n =
      ∑ k ∈ Finset.range (n + 1), ((-1 : ℝ) ^ (s - k) * (s.choose k : ℝ)) • (f ^ k).coeff n := by
  rw [sub_eq_add_neg, add_pow, finsetSum_coeff]
  rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : s + 1 ≤ n + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [show f ^ k * (-1) ^ (s - k) * ((s.choose k : ℕ) : S[X]) =
        C ((-1 : S) ^ (s - k) * (s.choose k : S)) * f ^ k by simp [map_mul, map_pow, map_neg]; ring]
    rw [coeff_C_mul, Algebra.smul_def]
    simp
  · intro k hk hk'
    simp only [Finset.mem_range] at hk hk'
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem coeff_zero_charpolyRev {R : Type} [CommRing R] {N : ℕ} (M : Matrix (Fin N) (Fin N) R) :
    M.charpolyRev.coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]

def newtonPoly {R : Type} [CommRing R] {N : ℕ} (M : Matrix (Fin N) (Fin N) R) (m : ℕ) : R[X] :=
  ∑ i ∈ Finset.range (m + 1), C (-(M ^ (i + 1)).trace) * X ^ i

theorem coeff_newtonPoly {R : Type} [CommRing R] {N : ℕ} (M : Matrix (Fin N) (Fin N) R) (m k : ℕ)
    (hk : k ≤ m) : (newtonPoly M m).coeff k = -(M ^ (k + 1)).trace := by
  simp only [newtonPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range, Nat.lt_succ_of_le hk]

theorem X_pow_dvd_derivative_sub {R : Type} [CommRing R] {N : ℕ} (M : Matrix (Fin N) (Fin N) R) (m : ℕ) :
    (X : R[X]) ^ (m + 1) ∣ derivative M.charpolyRev - newtonPoly M m * M.charpolyRev := by
  rw [X_pow_dvd_iff]
  intro d hd
  have hN := GlobalTheory.natCast_mul_coeff_charpolyRev M (d + 1)
  rw [coeff_sub, coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_congr rfl (fun k hk => by
    rw [coeff_newtonPoly M m k (by simp only [Finset.mem_range] at hk; omega)])]
  simp only [Nat.add_sub_cancel, neg_mul, Finset.sum_neg_distrib] at hN ⊢
  push_cast at hN
  linear_combination hN

def logTrunc {S : Type} [CommRing S] [Algebra ℝ S] (m : ℕ) (f : S[X]) : S[X] :=
  ∑ s ∈ Finset.range (m + 1), C (algebraMap ℝ S ((-1) ^ s / ((s : ℝ) + 1))) * (f - 1) ^ (s + 1)

theorem mul_derivative_logTrunc {S : Type} [CommRing S] [Algebra ℝ S] (m : ℕ) (f : S[X]) :
    f * derivative (logTrunc m f) = derivative f * (1 - (-(f - 1)) ^ (m + 1)) := by
  have hs : ∀ s : ℕ, C (algebraMap ℝ S ((-1) ^ s / ((s : ℝ) + 1))) * C ((s : S) + 1) = (-1) ^ s := by
    intro s
    rw [← C_mul, show ((s : S) + 1) = algebraMap ℝ S ((s : ℝ) + 1) by simp, ← map_mul,
      div_mul_cancel₀ _ (by positivity)]
    simp
  have hD : derivative (logTrunc m f) = (∑ s ∈ Finset.range (m + 1), (-(f - 1)) ^ s) * derivative f := by
    simp only [logTrunc, derivative_sum, derivative_C_mul, derivative_pow_succ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [derivative_sub, derivative_one, sub_zero, neg_pow (f - 1) s]
    linear_combination ((f - 1) ^ s * derivative f) * hs s
  have hg := mul_neg_geom_sum (-(f - 1)) (m + 1)
  rw [hD]
  linear_combination (derivative f) * hg

theorem coeff_logTrunc_charpolyRev {S : Type} [CommRing S] [Algebra ℝ S] {N : ℕ}
    (L : Matrix (Fin N) (Fin N) S) (m : ℕ) :
    ((m : S) + 1) * (logTrunc m (Matrix.charpolyRev (-L))).coeff (m + 1) =
      (-1) ^ m * (L ^ (m + 1)).trace := by
  set f := Matrix.charpolyRev (-L) with hf
  have hX : (X : S[X]) ∣ f - 1 := by
    simp [X_dvd_iff, hf, coeff_zero_charpolyRev]
  have h1 := X_pow_dvd_derivative_sub (-L) m
  rw [← hf] at h1
  have h2 : (X : S[X]) ^ (m + 1) ∣ derivative f * (-(f - 1)) ^ (m + 1) :=
    Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (dvd_neg.2 hX) (m + 1)) _
  have h3 : (X : S[X]) ^ (m + 1) ∣ f * (derivative (logTrunc m f) - newtonPoly (-L) m) := by
    have e : f * (derivative (logTrunc m f) - newtonPoly (-L) m) =
        (derivative f - newtonPoly (-L) m * f) - derivative f * (-(f - 1)) ^ (m + 1) := by
      linear_combination mul_derivative_logTrunc m f
    rw [e]
    exact dvd_sub h1 h2
  have hcop : IsCoprime (X : S[X]) f := by
    obtain ⟨h, hh⟩ := hX
    exact ⟨-h, 1, by linear_combination hh⟩
  have h4 := (X_pow_dvd_iff.1 (hcop.pow_left.dvd_of_dvd_mul_left h3)) m (by omega)
  rw [coeff_sub, coeff_derivative, coeff_newtonPoly (-L) m m le_rfl] at h4
  have ht : ((-L) ^ (m + 1)).trace = -((-1) ^ m * (L ^ (m + 1)).trace) := by
    rw [show -L = (-1 : S) • L by simp, _root_.smul_pow, Matrix.trace_smul, smul_eq_mul, pow_succ]
    ring
  linear_combination h4 - ht

end LogTrace


open LogTrace in
theorem trace_pow_eq_sum_smul_coeff_charpolyRev_pow :
    ∀ n : ℕ, 1 ≤ n → ∃ c : ℕ → ℝ, ∀ (S : Type) [CommRing S] [Algebra ℝ S] (N : ℕ)
      (L : Matrix (Fin N) (Fin N) S),
      ∑ k ∈ Finset.range (n + 1), c k • ((Matrix.charpolyRev (-L)) ^ k).coeff n = (L ^ n).trace := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨fun k => ∑ s ∈ Finset.range (m + 1),
    ((-1 : ℝ) ^ m * ((m : ℝ) + 1) * ((-1) ^ s / ((s : ℝ) + 1))) *
      ((-1 : ℝ) ^ (s + 1 - k) * ((s + 1).choose k : ℝ)), ?_⟩
  intro S _ _ N L
  have key := coeff_logTrunc_charpolyRev L m
  set f := Matrix.charpolyRev (-L)
  have hsq : ((-1 : S) ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; simp
  calc ∑ k ∈ Finset.range (m + 1 + 1), (∑ s ∈ Finset.range (m + 1),
        ((-1 : ℝ) ^ m * ((m : ℝ) + 1) * ((-1) ^ s / ((s : ℝ) + 1))) *
          ((-1 : ℝ) ^ (s + 1 - k) * ((s + 1).choose k : ℝ))) • (f ^ k).coeff (m + 1)
      = ∑ s ∈ Finset.range (m + 1), ((-1 : ℝ) ^ m * ((m : ℝ) + 1) * ((-1) ^ s / ((s : ℝ) + 1))) •
          ∑ k ∈ Finset.range (m + 1 + 1),
            ((-1 : ℝ) ^ (s + 1 - k) * ((s + 1).choose k : ℝ)) • (f ^ k).coeff (m + 1) := by
        simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
    _ = ∑ s ∈ Finset.range (m + 1), ((-1 : ℝ) ^ m * ((m : ℝ) + 1) * ((-1) ^ s / ((s : ℝ) + 1))) •
          ((f - 1) ^ (s + 1)).coeff (m + 1) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [coeff_sub_one_pow f (s + 1) (m + 1) (by simp only [Finset.mem_range] at hs; omega)]
    _ = ((-1 : ℝ) ^ m * ((m : ℝ) + 1)) • (logTrunc m f).coeff (m + 1) := by
        simp only [logTrunc, finsetSum_coeff, coeff_C_mul, Finset.smul_sum, ← Algebra.smul_def,
          smul_smul]
    _ = (L ^ (m + 1)).trace := by
        rw [Algebra.smul_def]
        simp only [map_mul, map_pow, map_neg, map_one, map_add (f := _), map_natCast]
        linear_combination (-1 : S) ^ m * key + (L ^ (m + 1)).trace * hsq

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerProductRealSpanMulMem
section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem trSpan_mul : ∀ {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (w w' : ℕ)
    (f g : Mat m S → S), f ∈ TrSpan m w S → g ∈ TrSpan m w' S → f * g ∈ TrSpan m (w + w') S := by
  intro ι m S _ _ w w' f g hf hg
  induction hf using Submodule.span_induction with
  | mem x hx =>
    induction hg using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl1, hlw, rfl⟩ := hx
      obtain ⟨l', hl1', hlw', rfl⟩ := hy
      apply Submodule.subset_span
      refine ⟨l ++ l', ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact hl1 x h
        · exact hl1' x h
      · simp [List.map_append, List.sum_append, hlw, hlw']
      · funext A
        simp [trProd, List.map_append, List.prod_append]
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul a y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hy
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hx

end GlobalTheory.GoodMetric.ChernSpan
end

