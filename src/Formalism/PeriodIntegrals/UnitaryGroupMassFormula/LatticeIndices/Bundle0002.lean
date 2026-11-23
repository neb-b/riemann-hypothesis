module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0001
public import Formalism.SatakeDualWeyl.Statement

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GenOfTwo
section
noncomputable section

namespace MassDataIdxEmb

open NumberField IsDedekindDomain Polynomial

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem mem_iff_algebraMap_mem_of_liesOver (P : Ideal (𝓞 E)) (q : Ideal (𝓞 F)) [P.LiesOver q]
    (c : 𝓞 F) : c ∈ q ↔ algebraMap (𝓞 F) (𝓞 E) c ∈ P := by
  rw [Ideal.over_def P q]
  exact Iff.rfl

private theorem exists_mem_not_mem_of_ne_of_isMaximal {R : Type*} [CommRing R] (Q Q' : Ideal R)
    [hQ : Q.IsMaximal] [hQ' : Q'.IsMaximal] (hne : Q ≠ Q') : ∃ a ∈ Q, a ∉ Q' := by
  by_contra h
  push Not at h
  exact hne (hQ.eq_of_le hQ'.ne_top (fun x hx => h x hx))

theorem gen_of_two (h2 : Module.finrank F E = 2) (p : HeightOneSpectrum (𝓞 F)) (Q Q' : Ideal (𝓞 E)) [hQ : Q.IsMaximal]
    [hQ' : Q'.IsMaximal] (hne : Q ≠ Q') [Q.LiesOver p.asIdeal] [Q'.LiesOver p.asIdeal] :
    ∃ a : 𝓞 E, ∃ c0 c1 : 𝓞 F, (∀ c : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) c ≠ a) ∧
      a * a + algebraMap (𝓞 F) (𝓞 E) c1 * a + algebraMap (𝓞 F) (𝓞 E) c0 = 0 ∧
      minpoly (𝓞 F) a = X ^ 2 + C c1 * X + C c0 ∧ (minpoly (𝓞 F) a).natDegree = 2 ∧
      c0 ∈ p.asIdeal ∧ c1 ∉ p.asIdeal := by
  obtain ⟨a, ha, ha'⟩ := exists_mem_not_mem_of_ne_of_isMaximal Q Q' hne
  have hnot : ∀ c : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) c ≠ a := by
    intro c hc
    apply ha'
    have hcQ : c ∈ p.asIdeal := (mem_iff_algebraMap_mem_of_liesOver Q p.asIdeal c).2 (by rw [hc]; exact ha)
    rw [← hc]
    exact (mem_iff_algebraMap_mem_of_liesOver Q' p.asIdeal c).1 hcQ
  have hint_r : IsIntegral (𝓞 F) a := Algebra.IsIntegral.isIntegral a
  have hFE : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  have hfield : minpoly F (algebraMap (𝓞 E) E a) = (minpoly (𝓞 F) a).map (algebraMap (𝓞 F) F) :=
    minpoly.isIntegrallyClosed_eq_field_fractions F E hint_r
  have hle : (minpoly (𝓞 F) a).natDegree ≤ 2 := by
    have h : (minpoly F (algebraMap (𝓞 E) E a)).natDegree ≤ Module.finrank F E := by
      apply minpoly.natDegree_le
    rw [hfield, (minpoly.monic hint_r).natDegree_map, h2] at h
    exact h
  have hpos : 0 < (minpoly (𝓞 F) a).natDegree := minpoly.natDegree_pos hint_r
  have hne1 : (minpoly (𝓞 F) a).natDegree ≠ 1 := by
    intro h1
    have hX := (minpoly.monic hint_r).eq_X_add_C h1
    have hev := minpoly.aeval (𝓞 F) a
    rw [hX] at hev
    simp only [map_add (f := _), aeval_X, aeval_C] at hev
    apply hnot (-(minpoly (𝓞 F) a).coeff 0)
    rw [map_neg]
    linear_combination -hev
  have hdeg : (minpoly (𝓞 F) a).natDegree = 2 := by omega
  have hP : minpoly (𝓞 F) a =
      X ^ 2 + C ((minpoly (𝓞 F) a).coeff 1) * X + C ((minpoly (𝓞 F) a).coeff 0) := by
    refine (minpoly.monic hint_r).as_sum.trans ?_
    rw [hdeg]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, mul_one,
      zero_add]
    ring
  have hev := minpoly.aeval (𝓞 F) a
  rw [hP] at hev
  simp only [map_add (f := _), map_mul, map_pow, aeval_X, aeval_C] at hev
  have heq : a * a + algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 1) * a +
      algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 0) = 0 := by
    linear_combination hev
  have hc0 : (minpoly (𝓞 F) a).coeff 0 ∈ p.asIdeal := by
    refine (mem_iff_algebraMap_mem_of_liesOver Q p.asIdeal _).2 ?_
    have h : algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 0) =
        -(a * (a + algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 1))) := by
      linear_combination heq
    rw [h]
    exact neg_mem (Q.mul_mem_right _ ha)
  have hc1 : (minpoly (𝓞 F) a).coeff 1 ∉ p.asIdeal := by
    intro h
    have h1 := (mem_iff_algebraMap_mem_of_liesOver Q' p.asIdeal _).1 h
    have h0 := (mem_iff_algebraMap_mem_of_liesOver Q' p.asIdeal _).1 hc0
    have haa : a * a ∈ Q' := by
      have h' : a * a = -(algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 1) * a +
          algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 0)) := by
        linear_combination heq
      rw [h']
      exact neg_mem (add_mem (Q'.mul_mem_right _ h1) h0)
    rcases hQ'.isPrime.mem_or_mem haa with h | h <;> exact ha' h
  exact ⟨a, _, _, hnot, heq, hP, hdeg, hc0, hc1⟩

private theorem finitePlace_embedding_eq_algebraMap (p : HeightOneSpectrum (𝓞 F)) (k : F) :
    FinitePlace.embedding p k = algebraMap F (p.adicCompletion F) k := rfl

private theorem norm_algebraMap_adicCompletion_lt_one_of_mem (p : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F)
    (hc : c ∈ p.asIdeal) : ‖algebraMap (𝓞 F) (p.adicCompletion F) c‖ < 1 := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (p.adicCompletion F), ← finitePlace_embedding_eq_algebraMap]
  exact (FinitePlace.norm_lt_one_iff_mem F p c).2 hc

private theorem norm_algebraMap_adicCompletion_eq_one_of_not_mem (p : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F)
    (hc : c ∉ p.asIdeal) : ‖algebraMap (𝓞 F) (p.adicCompletion F) c‖ = 1 := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (p.adicCompletion F), ← finitePlace_embedding_eq_algebraMap]
  exact (FinitePlace.norm_eq_one_iff_notMem F p c).2 hc

theorem emb_of_two (h2 : Module.finrank F E = 2) (p : HeightOneSpectrum (𝓞 F)) (Q Q' : Ideal (𝓞 E))
    [Q.IsMaximal] [Q'.IsMaximal] (hne : Q ≠ Q') [Q.LiesOver p.asIdeal] [Q'.LiesOver p.asIdeal] :
    Nonempty (E →ₐ[F] p.adicCompletion F) := by
  obtain ⟨a, c0, c1, -, -, hP, hdeg, hc0, hc1⟩ := gen_of_two h2 p Q Q' hne
  have hint_r : IsIntegral (𝓞 F) a := Algebra.IsIntegral.isIntegral a
  have hFE : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  have hfield : minpoly F (algebraMap (𝓞 E) E a) = (minpoly (𝓞 F) a).map (algebraMap (𝓞 F) F) :=
    minpoly.isIntegrallyClosed_eq_field_fractions F E hint_r
  have hbint : IsIntegral F (algebraMap (𝓞 E) E a) := IsIntegral.of_finite F _
  have htop : IntermediateField.adjoin F {algebraMap (𝓞 E) E a} = ⊤ := by
    rw [Field.primitive_element_iff_minpoly_natDegree_eq, hfield,
      (minpoly.monic hint_r).natDegree_map, hdeg, h2]
  obtain ⟨x, hx⟩ := quad_root
    (algebraMap (𝓞 F) (p.adicCompletion F) c0) (algebraMap (𝓞 F) (p.adicCompletion F) c1)
    (norm_algebraMap_adicCompletion_eq_one_of_not_mem p c1 hc1) (norm_algebraMap_adicCompletion_lt_one_of_mem p c0 hc0)
  have hroot : aeval x (minpoly F (algebraMap (𝓞 E) E a)) = 0 := by
    rw [hfield, aeval_map_algebraMap F, hP]
    simp only [map_add (f := _), map_mul, map_pow, aeval_X, aeval_C]
    linear_combination hx
  have hpb : aeval x (minpoly F (IntermediateField.adjoin.powerBasis hbint).gen) = 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]
    exact hroot
  let e : ↥(IntermediateField.adjoin F {algebraMap (𝓞 E) E a}) ≃ₐ[F] E :=
    (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  exact ⟨((IntermediateField.adjoin.powerBasis hbint).lift x hpb).comp e.symm.toAlgHom⟩

end MassDataIdxEmb
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Imports
section
noncomputable section

namespace MassDataIdxFrA

open Matrix

variable {F k : Type} [Field F] [Field k] (O : ValuationSubring F) (π : O →+* k) (γ : O)
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem clause_iff (hker : RingHom.ker π = Ideal.span {γ}) (Y : Matrix ι ι O) {β : Type} (u : β → ι → F)
    (pos : β → ι) (hu : ∀ b, ∃ z, IntVec O z ∧ u b = Pi.single (pos b) 1 + (γ : F) • z) (s : Set β)
    (w : ι → F) (j : ι) (hw : ∃ z, IntVec O z ∧ w = Pi.single j 1 + (γ : F) • z) :
    CongSpan O γ (u '' s) ((Y.map ((↑) : O → F) - 1) *ᵥ w) ↔
      ∀ i, i ∉ pos '' s → π (Y i j) = if i = j then 1 else 0 := by
  classical
  have hdiv : ∀ a : O, π a = 0 ↔ ∃ c : O, a = γ * c := by
    intro a
    rw [← RingHom.mem_ker, hker, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [← hc, mul_comm]⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [hc, mul_comm]⟩
  have hsm : ∀ (a : O) (x : ι → F), a • x = (a : F) • x := fun a x => rfl
  obtain ⟨z, hz, rfl⟩ := hw
  set Y' := Y.map ((↑) : O → F) with hY'
  let cO : ι → O := fun i => Y i j - (if i = j then 1 else 0)
  have hcO : ∀ i, (cO i : F) = (Y i j : F) - (if i = j then 1 else 0) := by
    intro i
    by_cases hij : i = j <;> simp [cO, hij]
  have hcol : (Y' - 1) *ᵥ Pi.single j (1 : F) = ∑ i, (cO i : F) • Pi.single i (1 : F) := by
    ext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, hcO]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, hY', Matrix.one_apply]
  have hint : ∀ i, ((Y' - 1) *ᵥ z) i ∈ O := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.one_apply, hY', Matrix.map_apply]
    refine _root_.sum_mem fun l _ => mul_mem (sub_mem (Y i l).2 ?_) (hz l)
    split_ifs
    · exact one_mem O
    · exact zero_mem O
  have hentry : ∀ i, ((Y' - 1) *ᵥ (Pi.single j 1 + (γ : F) • z)) i =
      (cO i : F) + (γ : F) * ((Y' - 1) *ᵥ z) i := by
    intro i
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcol,
      Finset.sum_apply]
    simp [Pi.single_apply]
  constructor
  · rintro ⟨W, hW, z', hz', hv⟩ i hi
    have key : ∀ v ∈ Submodule.span O (u '' s), ∃ c : O, v i = (γ : F) * c := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, hb, rfl⟩ := hx
        obtain ⟨zb, hzb, hub⟩ := hu b
        refine ⟨⟨zb i, hzb i⟩, ?_⟩
        have hne : i ≠ pos b := fun h => hi ⟨b, hb, h.symm⟩
        simp [hub, Pi.single_apply, hne]
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨c1, h1⟩ := hx
        obtain ⟨c2, h2⟩ := hy
        exact ⟨c1 + c2, by rw [Pi.add_apply, h1, h2]; push_cast; ring⟩
      | smul a x _ hx =>
        obtain ⟨c, h⟩ := hx
        refine ⟨a * c, ?_⟩
        rw [hsm, Pi.smul_apply, smul_eq_mul, h]
        push_cast
        ring
    obtain ⟨c, hc⟩ := key W hW
    have hvi := congrFun hv i
    rw [hentry i, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc] at hvi
    have hO : cO i = γ * ⟨(c : F) + z' i - ((Y' - 1) *ᵥ z) i,
        sub_mem (add_mem c.2 (hz' i)) (hint i)⟩ := by
      apply Subtype.ext
      show (cO i : F) = (γ : F) * ((c : F) + z' i - ((Y' - 1) *ᵥ z) i)
      linear_combination hvi
    have h0 := (hdiv _).2 ⟨_, hO⟩
    simp only [cO, map_sub, sub_eq_zero] at h0
    rw [h0]
    split_ifs <;> simp
  · intro hcond
    have hsel : ∀ i, i ∈ pos '' s → ∃ b, b ∈ s ∧ pos b = i := fun i hi => hi
    choose bsel hbs hpos using hsel
    have hout : ∀ i, i ∉ pos '' s → ∃ e : O, cO i = γ * e := by
      intro i hi
      apply (hdiv _).1
      simp only [cO, map_sub, hcond i hi]
      split_ifs <;> simp
    choose dsel hdsel using hout
    choose zb hzb hub using hu
    refine ⟨∑ i, (if h : i ∈ pos '' s then cO i • u (bsel i h) else 0), ?_,
      ∑ i, ((if h : i ∈ pos '' s then 0 else (dsel i h : F) • Pi.single i (1 : F)) -
        (if h : i ∈ pos '' s then (cO i : F) • zb (bsel i h) else 0)) + (Y' - 1) *ᵥ z, ?_, ?_⟩
    · refine _root_.sum_mem fun i _ => ?_
      split_ifs with h
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨bsel i h, hbs i h, rfl⟩)
      · exact Submodule.zero_mem _
    · intro l
      rw [Pi.add_apply, Finset.sum_apply]
      refine add_mem (_root_.sum_mem fun i _ => ?_) (hint l)
      rw [Pi.sub_apply]
      refine sub_mem ?_ ?_
      · split_ifs with h
        · exact zero_mem O
        · rw [Pi.smul_apply, smul_eq_mul]
          exact mul_mem (dsel i h).2 (by rw [Pi.single_apply]; split_ifs; exacts [one_mem O, zero_mem O])
      · split_ifs with h
        · rw [Pi.smul_apply, smul_eq_mul]
          exact mul_mem (cO i).2 (hzb _ l)
        · exact zero_mem O
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hcol, smul_add, Finset.smul_sum, ← add_assoc,
        ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : i ∈ pos '' s
      · simp only [h, dif_pos, hsm, hub, hpos i h, sub_zero, zero_sub, smul_add, smul_neg, smul_smul]
        rw [mul_comm]
        abel
      · simp only [h, dif_neg, not_false_eq_true, sub_zero, zero_add, smul_smul]
        rw [hdsel i h]
        push_cast
        rfl

end MassDataIdxFrA
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedCore
section
noncomputable section

namespace MassDataIdxCore

open Matrix

variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K)

def t1 : T →+* K := (RingHom.fst K K).comp θ.toAlgHom.toRingHom

def t2 : T →+* K := (RingHom.snd K K).comp θ.toAlgHom.toRingHom

theorem firstSplit_apply (t : T) : t1 θ t = (θ t).1 := rfl
theorem secondSplit_apply (t : T) : t2 θ t = (θ t).2 := rfl

variable {θ} {s : T →+* T} (hs : ∀ t, θ (s t) = (θ t).swap)
include hs

theorem firstSplit_conj (t : T) : t1 θ (s t) = t2 θ t := by
  rw [firstSplit_apply, secondSplit_apply, hs]
  rfl
theorem secondSplit_conj (t : T) : t2 θ (s t) = t1 θ t := by
  rw [firstSplit_apply, secondSplit_apply, hs]
  rfl

variable {n : Type} [Fintype n] [DecidableEq n]

theorem group_law_jacobian_eq (J : Matrix n n T) (hJ : Formalism.UG.cT s J = J) : J.map (t2 θ) = (J.map (t1 θ))ᵀ := by
  ext i j
  have hij := congrArg (fun M : Matrix n n T => M i j) hJ
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at hij
  simp only [Matrix.map_apply, Matrix.transpose_apply]
  rw [← hij, secondSplit_conj hs]

end MassDataIdxCore
end
end

