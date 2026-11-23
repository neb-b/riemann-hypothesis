module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0005
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GroupLawPowerSeries
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChLaw

private lemma nil_of_mem_span {S : Type} [CommRing S] {s : Set S} (hs : ∀ a ∈ s, IsNilpotent a)
    {c : S} (hc : c ∈ Ideal.span s) : IsNilpotent c := by
  have h : Ideal.span s ≤ nilradical S := Ideal.span_le.2 fun a ha => mem_nilradical.2 (hs a ha)
  exact mem_nilradical.1 (h hc)

theorem groupLaw_powerSeries :
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (c : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (κ → S) → S),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : κ → S),
      (∀ i, IsNilpotent (a i)) → φ (c S a) = c S' (fun i => φ (a i))) →
    ∃ f : MvPowerSeries κ R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (∀ i, IsNilpotent (a i)) → c S a = nEval f a) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (g : ℕ) (x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)),
    ((∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : Fin g → S),
        (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i))) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
        (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)) →
    ∃ F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) →
      (∀ k, fAdd F a b k ∈ Ideal.span (Set.range a ∪ Set.range b)) ∧ x S a * x S b = x S (fAdd F a b)) := by
  classical
  intro _ h2 R₀ _ G _ _ g x ⟨h0, hnat, hinj, hsur⟩
  have hex : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → ∃ c : Fin g → S,
        (∀ k, c k ∈ Ideal.span (Set.range a ∪ Set.range b)) ∧ (∀ k, IsNilpotent (c k)) ∧
        x S a * x S b = x S c := by
    intro S _ _ a b ha hb
    set I : Ideal S := Ideal.span (Set.range a ∪ Set.range b) with hI
    have hnil : ∀ c ∈ I, IsNilpotent c := fun c hc =>
      nil_of_mem_span (by rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩); exacts [ha i, hb i]) hc
    have hker : ∀ c, c ∈ RingHom.ker (Ideal.Quotient.mkₐ R₀ I) ↔ c ∈ I := fun c => by
      rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    have hz : spMap (Ideal.Quotient.mkₐ R₀ I) ≫ (x S a * x S b) = 1 := by
      have ea : (fun i => Ideal.Quotient.mkₐ R₀ I (a i)) = 0 := funext fun i =>
        (hker _).2 (Ideal.subset_span (Or.inl ⟨i, rfl⟩))
      have eb : (fun i => Ideal.Quotient.mkₐ R₀ I (b i)) = 0 := funext fun i =>
        (hker _).2 (Ideal.subset_span (Or.inr ⟨i, rfl⟩))
      rw [MonObj.comp_mul, hnat _ _ _ a ha, hnat _ _ _ b hb, ea, eb, h0, _root_.mul_one]
    obtain ⟨c, hc, hzc⟩ := hsur S (S ⧸ I) (Ideal.Quotient.mkₐ R₀ I)
      (Ideal.Quotient.mkₐ_surjective R₀ I) (fun c hc => hnil c ((hker c).1 hc)) _ hz
    exact ⟨c, fun k => (hker _).1 (hc k), fun k => hnil _ ((hker _).1 (hc k)), hzc⟩
  choose cc hc1 hc2 hc3 using hex
  have hF : ∀ k : Fin g, ∃ f : MvPowerSeries (Fin g ⊕ Fin g) R₀,
      ∀ (S : Type) [CommRing S] [Algebra R₀ S] (u : Fin g ⊕ Fin g → S)
        (hu : ∀ i, IsNilpotent (u i)),
        cc S (fun i => u (Sum.inl i)) (fun i => u (Sum.inr i)) (fun _ => hu _) (fun _ => hu _) k =
          nEval f u := by
    intro k
    obtain ⟨f, hf⟩ := h2 (R₀ := R₀) (κ := Fin g ⊕ Fin g)
      (fun S _ _ u => if hu : ∀ i, IsNilpotent (u i) then
        cc S (fun i => u (Sum.inl i)) (fun i => u (Sum.inr i)) (fun _ => hu _) (fun _ => hu _) k
        else 0) (by
        intro S _ _ S' _ _ φ u hu
        have hu' : ∀ i, IsNilpotent (φ (u i)) := fun i => (hu i).map φ
        simp only [dif_pos hu, dif_pos hu']
        have := hinj S'
          (fun j => φ (cc S (fun i => u (Sum.inl i)) (fun i => u (Sum.inr i))
            (fun _ => hu _) (fun _ => hu _) j))
          (cc S' (fun i => φ (u (Sum.inl i))) (fun i => φ (u (Sum.inr i)))
            (fun _ => hu' _) (fun _ => hu' _))
          (fun j => (hc2 _ _ _ _ _ j).map φ) (hc2 _ _ _ _ _) (by
            rw [← hnat _ _ φ _ (hc2 _ _ _ _ _), ← hc3, ← hc3, MonObj.comp_mul,
              hnat _ _ φ _ (fun _ => hu _), hnat _ _ φ _ (fun _ => hu _)])
        exact congrFun this k)
    refine ⟨f, fun S _ _ u hu => ?_⟩
    have := hf S u hu
    simpa only [dif_pos hu] using this
  choose F hF using hF
  refine ⟨F, fun S _ _ a b ha hb => ?_⟩
  have e : fAdd F a b = cc S a b ha hb := by
    funext k
    have hu : ∀ i, IsNilpotent (Sum.elim a b i) := by
      rintro (i | i); exacts [ha i, hb i]
    exact (hF k S (Sum.elim a b) hu).symm
  rw [e]
  exact ⟨hc1 S a b ha hb, hc3 S a b ha hb⟩

end GlobalTheory.ChLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearSubstCoordinateIntegralOfDegreeLt
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm

theorem linPull_coord_int_of_degree_lt :
    ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (e : Fin N → I → C), (∀ j x, V.Ge 0 (e j x)) → ∀ μ : Fin N →₀ ℕ, μ.degree < V.l → ∀ c, V.Ge 0 (MvPowerSeries.coeff μ (linPull e (t c))) := by
  intro C _ V d I J _ _ G S t ht N e he μ hμ c
  have hz : ∀ b j, V.Ge 0 (S.co (Sum.elim (e j) (0 : J → C)) b) := fun b j =>
    S.co_int (fun n => by
      cases n with
      | inl x => exact he j x
      | inr κ => exact VF.Ge.zero 0) b
  obtain ⟨h0, h1, -⟩ := GlobalTheory.T.formalGroupCoordinates_pullback_linear_tangentBasis C V d I J G S t ht (Fin N) e
    (fun b j => S.co (Sum.elim (e j) (0 : J → C)) b)
    (fun c k b => if k = 0 then (if c = b then 1 else 0) else S.co (S.cur c k) b)
    (fun j x => (S.co_spec (Sum.elim (e j) (0 : J → C)) x).symm)
    (fun c b => by simp)
    (fun c k x hk => by
      have hk' : k ≠ 0 := by omega
      simp only [if_neg hk', Sys.al, S.cur_zero_inl]
      exact (S.co_spec (S.cur c k) x).symm)
  have h2 := h1 c μ
  rw [Finset.sum_range_succ', Finset.sum_eq_zero, zero_add] at h2
  · simp only [if_true, pow_zero, pow_one, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ] at h2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum]
    refine VF.Ge.sum fun j _ => ?_
    rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
    refine (hz c j).mul_int ?_
    split_ifs
    · exact VF.Ge.one
    · exact VF.Ge.zero 0
  · intro s _
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [MvPowerSeries.coeff_of_lt_order, mul_zero]
    refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (h0 b))
    have : V.l ≤ V.l ^ (s + 1) := Nat.le_self_pow (Nat.succ_ne_zero s) _
    exact_mod_cast lt_of_lt_of_le hμ this

end GlobalTheory.MainTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearSubstCoordinateWeightNonnegRadius
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm

theorem linPull_coord_weight_nonneg : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (e : Fin N → I → C), (∀ j x, V.Ge 0 (e j x)) → ∀ (c : I) (μ : Fin N →₀ ℕ), V.Ge (-((μ.degree : ℝ) / ((V.l : ℝ) - 1))) (MvPowerSeries.coeff μ (linPull e (t c))) := by
  intro C _ _ V d _ I J _ _ G S t hT N e he c μ

  have hU : ∀ i j, V.Ge 0 (S.U⁻¹ i j) := inv_int S.U (fun i j => S.U_int i j) S.unimod

  have hco : ∀ (h : I ⊕ J → C) (w : ℝ), (∀ k, V.Ge w (h (Sum.inl k))) → ∀ b, V.Ge w (S.co h b) := by
    intro h w hh b
    have hs := VF.Ge.sum (s := Finset.univ) (fun k _ => VF.Ge.mul (hh k) (hU k b))
    rw [add_zero] at hs
    exact hs

  obtain ⟨z, hze, hzi⟩ : ∃ z : I → Fin N → C,
      (∀ j x, e j x = ∑ b, z b j * S.tan b x) ∧ ∀ b j, V.Ge 0 (z b j) := by
    refine ⟨fun b j => S.co (Sum.elim (e j) 0) b, fun j x => ?_, fun b j => hco _ 0 (fun k => he j k) b⟩
    have hs := S.co_spec (Sum.elim (e j) 0) x
    simp only [Sys.U, Matrix.of_apply, Sum.elim_inl] at hs
    exact hs.symm

  obtain ⟨al, hal0, halk, hali⟩ : ∃ al : I → ℕ → I → C, (∀ c b, al c 0 b = if c = b then 1 else 0) ∧
      (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, al c k b * S.al b 0 x) ∧
      ∀ c (n : ℕ) b, V.Ge (-(n : ℝ)) (al c n b) := by
    refine ⟨fun c k b => if k = 0 then (if c = b then 1 else 0) else S.co (Sum.elim (S.al c k) 0) b,
      fun c b => if_pos rfl, ?_, ?_⟩
    · intro c k x hk
      have hk0 : k ≠ 0 := by omega
      have hs := S.co_spec (Sum.elim (S.al c k) 0) x
      simp only [Sys.U, Matrix.of_apply, Sum.elim_inl] at hs
      rw [← hs]
      refine Finset.sum_congr rfl fun b _ => ?_
      beta_reduce
      rw [if_neg hk0, Sys.al, S.cur_zero_inl]
    · intro c n b
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · beta_reduce
        rw [if_pos rfl, Nat.cast_zero, neg_zero]
        split_ifs
        · exact VF.Ge.one
        · exact VF.Ge.zero _
      · beta_reduce
        rw [if_neg (show n ≠ 0 by omega)]
        exact hco _ _ (fun k => lattice_inclusion_forms_injective G S c n (Sum.inl k)) b
  obtain ⟨h0, hlog, -⟩ := GlobalTheory.T.formalGroupCoordinates_pullback_linear_tangentBasis C V d I J G S t hT (Fin N) e z al hze hal0 halk

  let σ := Fintype.equivFin I
  have key := GlobalTheory.ExpWeight.ordGe_of_lgSum_eq_linear C V.v V.l V.l_prime V.v_l (Fintype.card I) N
    (fun a n b => al (σ.symm a) n (σ.symm b)) (fun a j => z (σ.symm a) j)
    (fun a => linPull e (t (σ.symm a)))
    (fun a b => by simp only [hal0, Equiv.apply_eq_iff_eq])
    (fun a n b => hali _ _ _)
    (fun a j => by
      have hz := hzi (σ.symm a) j
      unfold VF.Ge at hz
      rwa [WithTop.coe_zero] at hz)
    (fun a => h0 _) ?_ (σ c)
  · have hα := key μ
    simp only [Equiv.symm_apply_apply] at hα
    unfold VF.Ge
    refine le_trans ?_ hα
    refine WithTop.coe_le_coe.mpr ?_
    have hl : (1 : ℝ) < V.l := by exact_mod_cast V.l_prime.one_lt
    have hpos : (0 : ℝ) < 1 / ((V.l : ℝ) - 1) := by
      have : (0 : ℝ) < (V.l : ℝ) - 1 := by linarith
      positivity
    rw [← Finset.mul_sum, ← Nat.cast_sum, ← Finsupp.degree_eq_sum]
    have hd : ((μ.degree : ℕ) : ℝ) / ((V.l : ℝ) - 1) = 1 / ((V.l : ℝ) - 1) * (μ.degree : ℝ) := by ring
    rw [hd]
    linarith
  · intro b
    ext α
    show (∑ n ∈ Finset.range (α.degree + 1), ∑ a, al (σ.symm a) n (σ.symm b) *
      MvPowerSeries.coeff α (linPull e (t (σ.symm a)) ^ (V.l ^ n))) = _
    rw [← hlog (σ.symm b) α]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact Equiv.sum_comp σ.symm (fun a => al a n (σ.symm b) * MvPowerSeries.coeff α (linPull e (t a) ^ (V.l ^ n)))

end GlobalTheory.MainTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilpotentCoordinates
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilCoord

section Alg

variable {R : Type} [CommRing R] {n : ℕ} {B : Type} [CommRing B] [Algebra R B]

theorem ext_of_nil (π : MvPolynomial (Fin n) R →ₐ[R] B) (hπ : π.toRingHom.Etale)
    {A : Type} [CommRing A] [Algebra R A] (φ₁ φ₂ : B →ₐ[R] A)
    (h : ∀ b, IsNilpotent (φ₁ b - φ₂ b))
    (hs : ∀ j : Fin n, φ₁ (π (MvPolynomial.X j)) = φ₂ (π (MvPolynomial.X j))) : φ₁ = φ₂ := by
  letI : Algebra (MvPolynomial (Fin n) R) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) B := hπ
  let ρ : MvPolynomial (Fin n) R →ₐ[R] A := φ₁.comp π
  have hρ2 : φ₂.comp π = ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    exact (hs j).symm
  letI : Algebra (MvPolynomial (Fin n) R) A := ρ.toRingHom.toAlgebra
  let ψ₁ : B →ₐ[MvPolynomial (Fin n) R] A :=
    { φ₁.toRingHom with commutes' := fun p => rfl }
  let ψ₂ : B →ₐ[MvPolynomial (Fin n) R] A :=
    { φ₂.toRingHom with commutes' := fun p => AlgHom.congr_fun hρ2 p }
  obtain ⟨s, hsg⟩ := (inferInstance : Algebra.FiniteType (MvPolynomial (Fin n) R) B).out
  let J : Ideal A := Ideal.span ((fun b => φ₁ b - φ₂ b) '' (s : Set B))
  have hJ : IsNilpotent J := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical
      (Submodule.fg_span (s.finite_toSet.image _)), Ideal.span_le]
    rintro _ ⟨b, -, rfl⟩
    exact h b
  have : ψ₁ = ψ₂ := by
    apply Algebra.FormallyUnramified.lift_unique J hJ
    apply AlgHom.ext_of_adjoin_eq_top hsg
    intro b hb
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨b, hb, rfl⟩
  ext x
  exact AlgHom.congr_fun this x

theorem exists_of_nil (π : MvPolynomial (Fin n) R →ₐ[R] B) (hπ : π.toRingHom.Etale)
    {A : Type} [CommRing A] [Algebra R A] (e : B →ₐ[R] A) (a : Fin n → A)
    (ha : ∀ j, IsNilpotent (a j)) :
    ∃ φ : B →ₐ[R] A, (∀ b, IsNilpotent (φ b - e b)) ∧
      ∀ j, φ (π (MvPolynomial.X j)) = e (π (MvPolynomial.X j)) + a j := by
  letI : Algebra (MvPolynomial (Fin n) R) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) B := hπ
  let ρ : MvPolynomial (Fin n) R →ₐ[R] A :=
    MvPolynomial.aeval (fun j => e (π (MvPolynomial.X j)) + a j)
  letI : Algebra (MvPolynomial (Fin n) R) A := ρ.toRingHom.toAlgebra
  let J : Ideal A := Ideal.span (Set.range a)
  have hJ : IsNilpotent J := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical
      (Submodule.fg_span (Set.finite_range _)), Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    exact ha b
  let mk : A →ₐ[MvPolynomial (Fin n) R] A ⧸ J := Ideal.Quotient.mkₐ _ J
  have hf₀ : ((Ideal.Quotient.mkₐ R J).comp e).comp π = (Ideal.Quotient.mkₐ R J).comp ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ρ,
      MvPolynomial.aeval_X]
    rw [eq_comm, Ideal.Quotient.eq, add_sub_cancel_left]
    exact Ideal.subset_span ⟨j, rfl⟩
  let f₀ : B →ₐ[MvPolynomial (Fin n) R] A ⧸ J :=
    { ((Ideal.Quotient.mkₐ R J).comp e).toRingHom with
      commutes' := fun p => AlgHom.congr_fun hf₀ p }
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hker : IsNilpotent (RingHom.ker (mk : A →+* A ⧸ J)) := by
    have : RingHom.ker (mk : A →+* A ⧸ J) = J := Ideal.mk_ker
    rw [this]
    exact hJ
  let φ' := Algebra.FormallySmooth.liftOfSurjective f₀ mk hmk hker
  have hφ' : mk.comp φ' = f₀ := Algebra.FormallySmooth.comp_liftOfSurjective f₀ mk hmk hker
  have hc : ∀ p, φ' (π p) = ρ p := fun p => φ'.commutes p
  refine ⟨{ φ'.toRingHom with commutes' := fun r => ?_ }, fun b => ?_, fun j => ?_⟩
  · show φ' (algebraMap R B r) = _
    rw [← π.commutes, hc, ρ.commutes]
  · have e1 : Ideal.Quotient.mk J (φ' b) = Ideal.Quotient.mk J (e b) := AlgHom.congr_fun hφ' b
    rw [Ideal.Quotient.eq] at e1
    obtain ⟨N, hN⟩ := hJ
    refine ⟨N, ?_⟩
    have := Ideal.pow_mem_pow e1 N
    rw [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact this
  · show φ' (π _) = _
    rw [hc]
    exact MvPolynomial.aeval_X _ j

end Alg

theorem exists_etale_chart {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]
    [IsLocalRing R₀] (g : ℕ) (hG : SmoothOfRelativeDimension g G.hom) :
    ∃ (C : Chart G) (π : MvPolynomial (Fin g) R₀ →ₐ[R₀] Γ(G.left, C.U)), π.toRingHom.Etale := by
  let e0 : Spec (CommRingCat.of R₀) ⟶ G.left := (η[G]).left
  obtain ⟨U, hU, V, hV, hx, e, h⟩ :=
    hG.exists_isStandardSmoothOfRelativeDimension (e0 (IsLocalRing.closedPoint R₀))
  have hsp : ∀ p : PrimeSpectrum R₀, p ⤳ IsLocalRing.closedPoint R₀ := fun p =>
    (PrimeSpectrum.le_iff_specializes _ _).mp
      (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum R₀).isPrime.ne_top)
  have hw : e0 ≫ G.hom = 𝟙 _ := Over.w (η[G])
  have hU' : U = ⊤ := by
    rw [eq_top_iff]
    intro p _
    refine (hsp p).mem_open U.isOpen ?_
    have h1 : (e0 ≫ G.hom) (IsLocalRing.closedPoint R₀) ∈ U := by
      exact (Scheme.Hom.comp_apply e0 G.hom (IsLocalRing.closedPoint R₀)).symm ▸ e hx
    rw [hw] at h1
    exact h1
  subst hU'
  let C : Chart G := ⟨V, hV, fun p _ => (hsp p).mem_open (e0 ⁻¹ᵁ V).isOpen hx⟩
  have h2 : RingHom.IsStandardSmoothOfRelativeDimension g (alg0 C) :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of R₀)).symm.commRingCatIsoToRingEquiv h
  obtain ⟨π, hπ1, hπ2⟩ := h2.exists_etale_mvPolynomial
  clear_value C
  exact ⟨C, { π with commutes' := fun r => RingHom.congr_fun hπ1 r }, hπ2⟩

theorem nilpotent_coordinates :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] [IsLocalRing R₀] (g : ℕ), SmoothOfRelativeDimension g G.hom →
    ∃ x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G),
      (∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : Fin g → S),
        (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i))) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
        (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)) := by
  intro R₀ _ G _ _ _ g hG
  classical
  obtain ⟨C, π, hπ⟩ := exists_etale_chart G g hG
  have key : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S),
      ∃ φ : Γ(G.left, C.U) →ₐ[R₀] S, (∀ i, IsNilpotent (a i)) →
        (∀ b, IsNilpotent (φ b - algebraMap R₀ S (eps C b))) ∧
        ∀ j, φ (π (MvPolynomial.X j)) = algebraMap R₀ S (eps C (π (MvPolynomial.X j))) + a j := by
    intro S _ _ a
    by_cases ha : ∀ i, IsNilpotent (a i)
    · obtain ⟨φ, h⟩ := exists_of_nil π hπ ((Algebra.ofId R₀ S).comp (eps C)) a ha
      exact ⟨φ, fun _ => h⟩
    · exact ⟨(Algebra.ofId R₀ S).comp (eps C), fun h => absurd h ha⟩
  choose F hF using key
  have uniq : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S) (φ : Γ(G.left, C.U) →ₐ[R₀] S),
      (∀ i, IsNilpotent (a i)) → (∀ b, IsNilpotent (φ b - algebraMap R₀ S (eps C b))) →
      (∀ j, φ (π (MvPolynomial.X j)) = algebraMap R₀ S (eps C (π (MvPolynomial.X j))) + a j) →
      φ = F S a := by
    intro S _ _ a φ ha h1 h2
    refine ext_of_nil π hπ _ _ (fun b => ?_) (fun j => ?_)
    · have := (Commute.all _ _).isNilpotent_sub (h1 b) ((hF S a ha).1 b)
      rwa [sub_sub_sub_cancel_right] at this
    · rw [h2, (hF S a ha).2]
  refine ⟨fun S _ _ a => pt C (F S a), ?_, ?_, ?_, ?_⟩
  · intro S _ _
    show pt C (F S 0) = 1
    rw [← uniq S 0 ((Algebra.ofId R₀ S).comp (eps C)) (fun _ => IsNilpotent.zero)
      (fun b => by simp [Algebra.ofId_apply]) (fun j => by simp [Algebra.ofId_apply]), pt_eps]
  · intro S _ _ S' _ _ φ a ha
    show spMap φ ≫ pt C (F S a) = pt C (F S' _)
    rw [spMap_pt]
    congr 1
    refine uniq S' _ _ (fun i => (ha i).map φ) (fun b => ?_) (fun j => ?_)
    · have := ((hF S a ha).1 b).map φ
      rwa [map_sub, AlgHom.commutes] at this
    · rw [AlgHom.comp_apply, (hF S a ha).2, map_add (f := _), AlgHom.commutes]
  · intro S _ _ a b ha hb h
    have h1 : F S a = F S b := pt_injective C h
    funext j
    have h2 := (hF S a ha).2 j
    rw [h1, (hF S b hb).2 j] at h2
    exact (add_left_cancel h2).symm
  · intro S _ _ S' _ _ ρ hρ hn z hz
    rw [← pt_eps C S'] at hz
    obtain ⟨φ, rfl⟩ := exists_pt C z (le_preimage_of_nil C ρ hρ hn z _ hz)
    rw [spMap_pt] at hz
    have h1 := pt_injective C hz
    have h2 : ∀ b, φ b - algebraMap R₀ S (eps C b) ∈ RingHom.ker ρ := by
      intro b
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero]
      exact AlgHom.congr_fun h1 b
    refine ⟨fun j => φ (π (MvPolynomial.X j)) - algebraMap R₀ S (eps C (π (MvPolynomial.X j))),
      fun j => h2 _, ?_⟩
    show pt C φ = pt C (F S _)
    congr 1
    exact uniq S _ φ (fun j => hn _ (h2 _)) (fun b => hn _ (h2 b)) (fun j => by rw [add_sub_cancel])

end GlobalTheory.NilCoord
end

