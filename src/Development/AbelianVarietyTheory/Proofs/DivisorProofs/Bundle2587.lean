module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2423
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNormProdAevalEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PadicRootNorm

open Polynomial Filter Topology

variable {l : ℕ} [Fact l.Prime]

theorem norm_prod_map {β : Type*} (s : Multiset β) (f : β → PadicAlgCl l) :
    ‖(s.map f).prod‖ = (s.map fun a => ‖f a‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [norm_mul, ih]

open Classical in
theorem eventually_norm_prod (s : Multiset (PadicAlgCl l)) (M : ℚ_[l][X]) :
    ∀ᶠ n : ℕ in atTop, ‖(s.map fun a => aeval a (M + C ((l : ℚ_[l]) ^ n))).prod‖ =
      ‖(l : ℚ_[l])‖ ^ (n * (s.filter fun a => aeval a M = 0).card) *
        ((s.filter fun a => ¬ aeval a M = 0).map fun a => ‖aeval a M‖).prod := by
  have hl : Tendsto (fun n : ℕ => ‖(l : ℚ_[l])‖ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) Padic.norm_p_lt_one
  have hev : ∀ᶠ n : ℕ in atTop, ∀ a ∈ (s.filter fun a => ¬ aeval a M = 0).toFinset,
      ‖(l : ℚ_[l])‖ ^ n < ‖aeval a M‖ := by
    rw [Filter.eventually_all_finset]
    intro a ha
    have : aeval a M ≠ 0 := (Multiset.mem_filter.1 (Multiset.mem_toFinset.1 ha)).2
    exact (tendsto_order.1 hl).2 _ (norm_pos_iff.2 this)
  filter_upwards [hev] with n hn
  conv_lhs => rw [← Multiset.filter_add_not (fun a => aeval a M = 0) s]
  rw [Multiset.map_add (f := _), Multiset.prod_add, norm_mul, norm_prod_map, norm_prod_map]
  congr 1
  · rw [Multiset.map_congr rfl (g := fun _ => ‖(l : ℚ_[l])‖ ^ n), Multiset.map_const',
      Multiset.prod_replicate, ← pow_mul]
    intro a ha
    have h0 : aeval a M = 0 := (Multiset.mem_filter.1 ha).2
    rw [map_add (f := _), aeval_C, h0, zero_add, norm_algebraMap', norm_pow]
  · apply congrArg
    apply Multiset.map_congr rfl
    intro a ha
    have hlt := hn a (Multiset.mem_toFinset.2 ha)
    have hc : ‖algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℚ_[l]) ^ n)‖ = ‖(l : ℚ_[l])‖ ^ n := by
      rw [norm_algebraMap', norm_pow]
    rw [map_add (f := _), aeval_C, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hc]; exact hlt.ne'),
      hc, max_eq_left hlt.le]

open Classical in
theorem card_filter_eq (s t : Multiset (PadicAlgCl l))
    (h : ∀ F : ℚ_[l][X], ‖(s.map fun a => aeval a F).prod‖ = ‖(t.map fun a => aeval a F).prod‖)
    (M : ℚ_[l][X]) :
    (s.filter fun a => aeval a M = 0).card = (t.filter fun a => aeval a M = 0).card := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((eventually_norm_prod s M).and (eventually_norm_prod t M))
  set x := ‖(l : ℚ_[l])‖ with hxdef
  have hx0 : 0 < x := norm_pos_iff.2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have hx1 : x < 1 := Padic.norm_p_lt_one
  set k := (s.filter fun a => aeval a M = 0).card
  set k' := (t.filter fun a => aeval a M = 0).card
  set c := ((s.filter fun a => ¬ aeval a M = 0).map fun a => ‖aeval a M‖).prod
  set c' := ((t.filter fun a => ¬ aeval a M = 0).map fun a => ‖aeval a M‖).prod
  have hc' : 0 < c' := Multiset.prod_pos fun y hy => by
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hy
    exact norm_pos_iff.2 (Multiset.mem_filter.1 ha).2
  have e1 : x ^ (N * k) * c = x ^ (N * k') * c' := by
    rw [← (hN N le_rfl).1, ← (hN N le_rfl).2, h]
  have e2 : x ^ ((N + 1) * k) * c = x ^ ((N + 1) * k') * c' := by
    rw [← (hN (N + 1) (Nat.le_succ N)).1, ← (hN (N + 1) (Nat.le_succ N)).2, h]
  have e3 : x ^ k * (x ^ (N * k') * c') = x ^ k' * (x ^ (N * k') * c') := by
    calc x ^ k * (x ^ (N * k') * c') = x ^ k * (x ^ (N * k) * c) := by rw [e1]
      _ = x ^ ((N + 1) * k) * c := by rw [← _root_.mul_assoc, ← pow_add]; congr 2; ring
      _ = x ^ ((N + 1) * k') * c' := e2
      _ = x ^ k' * (x ^ (N * k') * c') := by rw [← _root_.mul_assoc, ← pow_add]; congr 2; ring
  have hne : x ^ (N * k') * c' ≠ 0 := by positivity
  exact pow_right_injective₀ hx0 hx1.ne (mul_right_cancel₀ hne e3)

theorem monic_eq_one_of_no_root {P : ℚ_[l][X]} (hP : P.Monic)
    (h : ∀ a : PadicAlgCl l, a ∉ P.aroots (PadicAlgCl l)) : P = 1 := by
  by_contra hne
  have hd : P.degree ≠ 0 := by
    intro hd
    exact hne (eq_one_of_monic_natDegree_zero hP (natDegree_eq_of_degree_eq_some hd))
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_aeval_eq_zero (PadicAlgCl l) P hd
  exact h a (mem_aroots.2 ⟨hP.ne_zero, ha⟩)

open Classical in
theorem exists_root_minpoly_eq_of_card_eq (P Q : ℚ_[l][X]) (hQ : Q ≠ 0)
    (hc : ∀ a : PadicAlgCl l, ((P.aroots (PadicAlgCl l)).filter fun b => aeval b (minpoly ℚ_[l] a) = 0).card =
      ((Q.aroots (PadicAlgCl l)).filter fun b => aeval b (minpoly ℚ_[l] a) = 0).card)
    (a : PadicAlgCl l) (ha : a ∈ P.aroots (PadicAlgCl l)) :
    ∃ b ∈ Q.aroots (PadicAlgCl l), minpoly ℚ_[l] a = minpoly ℚ_[l] b := by
  have hint : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  have h1 : 0 < ((P.aroots (PadicAlgCl l)).filter fun b => aeval b (minpoly ℚ_[l] a) = 0).card :=
    Multiset.card_pos_iff_exists_mem.2 ⟨a, Multiset.mem_filter.2 ⟨ha, minpoly.aeval _ _⟩⟩
  rw [hc a] at h1
  obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.1 h1
  obtain ⟨hbQ, hbM⟩ := Multiset.mem_filter.1 hb
  exact ⟨b, hbQ, minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hbM (minpoly.monic hint)⟩

open Classical in
theorem eq_of_card_filter (n : ℕ) : ∀ P Q : ℚ_[l][X], P.natDegree = n → P.Monic → Q.Monic →
    (∀ a : PadicAlgCl l, ((P.aroots (PadicAlgCl l)).filter fun b => aeval b (minpoly ℚ_[l] a) = 0).card =
      ((Q.aroots (PadicAlgCl l)).filter fun b => aeval b (minpoly ℚ_[l] a) = 0).card) → P = Q := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P Q hn hP hQ hc
  by_cases hr : ∃ a : PadicAlgCl l, a ∈ P.aroots (PadicAlgCl l)
  · obtain ⟨a, ha⟩ := hr
    have hint : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
    obtain ⟨b, hbQ, hab⟩ := exists_root_minpoly_eq_of_card_eq P Q hQ.ne_zero hc a ha
    have hMQ : minpoly ℚ_[l] a ∣ Q := by rw [hab]; exact minpoly.dvd _ _ (mem_aroots.1 hbQ).2
    have hMP : minpoly ℚ_[l] a ∣ P := minpoly.dvd _ _ (mem_aroots.1 ha).2
    have hM : (minpoly ℚ_[l] a).Monic := minpoly.monic hint
    have hMpos := minpoly.natDegree_pos hint
    obtain ⟨P', rfl⟩ := hMP
    obtain ⟨Q', rfl⟩ := hMQ
    have hP' := hM.of_mul_monic_left hP
    have hQ' := hM.of_mul_monic_left hQ
    have hdeg : (minpoly ℚ_[l] a * P').natDegree = (minpoly ℚ_[l] a).natDegree + P'.natDegree :=
      hM.natDegree_mul hP'
    rw [ih P'.natDegree (by omega) P' Q' rfl hP' hQ' ?_]
    intro b
    have h := hc b
    rw [aroots_mul hP.ne_zero, aroots_mul hQ.ne_zero, Multiset.filter_add, Multiset.filter_add,
      Multiset.card_add, Multiset.card_add] at h
    omega
  · push_neg at hr
    have hr' : ∀ b : PadicAlgCl l, b ∉ Q.aroots (PadicAlgCl l) := by
      intro b hb
      obtain ⟨a, haP, hab⟩ := exists_root_minpoly_eq_of_card_eq Q P hP.ne_zero (fun c => (hc c).symm) b hb
      have hint : IsIntegral ℚ_[l] b := Algebra.IsIntegral.isIntegral b
      exact hr a haP
    rw [monic_eq_one_of_no_root hP hr, monic_eq_one_of_no_root hQ hr']

theorem norm_eq_rat (s t : Multiset (PadicAlgCl l)) (hst : Multiset.card s = Multiset.card t)
    (h : ∀ F : ℤ[X], ‖(s.map fun a => aeval a F).prod‖ = ‖(t.map fun a => aeval a F).prod‖)
    (R : ℚ[X]) :
    ‖(s.map fun a => aeval a (R.map (algebraMap ℚ ℚ_[l]))).prod‖ =
      ‖(t.map fun a => aeval a (R.map (algebraMap ℚ ℚ_[l]))).prod‖ := by
  obtain ⟨b, hbmem, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) R
  set G := IsLocalization.integerNormalization (nonZeroDivisors ℤ) R
  have key : ∀ a : PadicAlgCl l, aeval a G = ((b : ℤ) : PadicAlgCl l) * aeval a (R.map (algebraMap ℚ ℚ_[l])) := by
    intro a
    rw [aeval_map_algebraMap, ← aeval_map_algebraMap ℚ a G, hb, map_zsmul, zsmul_eq_mul]
  have hb0 : ((b : ℤ) : PadicAlgCl l) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hbmem)
  have hG := h G
  simp only [key] at hG
  rw [Multiset.prod_map_mul, Multiset.prod_map_mul, Multiset.map_const', Multiset.map_const',
    Multiset.prod_replicate, Multiset.prod_replicate, norm_mul, norm_mul, hst] at hG
  exact mul_left_cancel₀ (norm_ne_zero_iff.2 (pow_ne_zero _ hb0)) hG

theorem norm_eq_all (s t : Multiset (PadicAlgCl l))
    (h : ∀ R : ℚ[X], ‖(s.map fun a => aeval a (R.map (algebraMap ℚ ℚ_[l]))).prod‖ =
      ‖(t.map fun a => aeval a (R.map (algebraMap ℚ ℚ_[l]))).prod‖)
    (F : ℚ_[l][X]) :
    ‖(s.map fun a => aeval a F).prod‖ = ‖(t.map fun a => aeval a F).prod‖ := by
  have hr : ∀ (n i : ℕ), ∃ q : ℚ, ‖F.coeff i - q‖ < 1 / ((n : ℝ) + 1) :=
    fun n i => Padic.rat_dense l _ (by positivity)
  choose r hr using hr
  set D := F.natDegree
  let R : ℕ → ℚ[X] := fun n => ∑ i ∈ Finset.range (D + 1), C (r n i) * Polynomial.X ^ i
  have hcoef : ∀ i, Tendsto (fun n => ((r n i : ℚ) : ℚ_[l])) atTop (𝓝 (F.coeff i)) := by
    intro i
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [norm_sub_rev]; exact (hr n i).le
  have hval : ∀ a : PadicAlgCl l, Tendsto (fun n => aeval a ((R n).map (algebraMap ℚ ℚ_[l])))
      atTop (𝓝 (aeval a F)) := by
    intro a
    have e : ∀ n, aeval a ((R n).map (algebraMap ℚ ℚ_[l])) =
        ∑ i ∈ Finset.range (D + 1), algebraMap ℚ_[l] (PadicAlgCl l) ((r n i : ℚ) : ℚ_[l]) * a ^ i := by
      intro n
      rw [aeval_map_algebraMap]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [R, map_sum]
    simp only [e]
    rw [aeval_eq_sum_range]
    simp only [Algebra.smul_def]
    exact tendsto_finsetSum _ fun i _ =>
      (((continuous_algebraMap ℚ_[l] (PadicAlgCl l)).tendsto _).comp (hcoef i)).mul_const _
  have hs := (tendsto_multiset_prod s fun a _ => hval a).norm
  have ht := (tendsto_multiset_prod t fun a _ => hval a).norm
  exact tendsto_nhds_unique hs (ht.congr fun n => (h (R n)).symm)

theorem card_aroots (P : ℚ_[l][X]) : Multiset.card (P.aroots (PadicAlgCl l)) = P.natDegree := by
  rw [aroots_def, IsAlgClosed.card_roots_eq_natDegree, natDegree_map]

theorem eq_of_norm_prod_aeval_eq : ∀ (l : ℕ) [Fact l.Prime] (P Q : Polynomial ℚ_[l]), P.Monic → Q.Monic →
    P.natDegree = Q.natDegree →
    (∀ F : Polynomial ℤ, ‖((P.aroots (PadicAlgCl l)).map (fun a => Polynomial.aeval a F)).prod‖ =
      ‖((Q.aroots (PadicAlgCl l)).map (fun a => Polynomial.aeval a F)).prod‖) → P = Q := by
  intro l _ P Q hP hQ hdeg h
  classical
  have hcard : Multiset.card (P.aroots (PadicAlgCl l)) = Multiset.card (Q.aroots (PadicAlgCl l)) := by
    rw [card_aroots, card_aroots, hdeg]
  have hall := norm_eq_all _ _ (norm_eq_rat _ _ hcard h)
  exact eq_of_card_filter _ P Q rfl hP hQ fun a => card_filter_eq _ _ hall _

end GlobalTheory.PadicRootNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChartProductAtClosedPointClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.EtChart

theorem mvPolynomial_stdSmooth (R : Type) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  let P₀ : Algebra.Presentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := Algebra.Generators.mvPolynomial R (Fin n)
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  exact P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])


set_option backward.isDefEq.respectTransparency false in
theorem affineSpace_smooth (S : Scheme.{0}) (n : ℕ) : Smooth (𝔸(Fin n; S) ↘ S) := by
  have : SmoothOfRelativeDimension n (𝔸(Fin n; S) ↘ S) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} n
    refine MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension n) _ _ ?_
    have := isIso_of_isTerminal specULiftZIsTerminal.{0} terminalIsTerminal (terminal.from _)
    rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C)),
      MorphismProperty.cancel_right_of_respectsIso (P := @SmoothOfRelativeDimension n),
      HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
    refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).2
      (mvPolynomial_stdSmooth (ULift ℤ) n)
  exact SmoothOfRelativeDimension.smooth n _

end GlobalTheory.Mum.EtChart

namespace GlobalTheory.Mum

theorem etale_chart_at_closed_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), IsSeparated b → LocallyOfFiniteType b → IsProper a → (∀ V : P'.Opens, Function.Bijective (a.app V).hom) → a ≫ b = X.ι ≫ E.f → Function.Bijective M.π.appTop.hom → Surjective M.π → ∀ x : P', IsClosed ({x} : Set P') → (b ≫ PSpace.str R E.N) x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X.toScheme), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ X.ι ≫ E.H.ι ≫ G'.hom = p' ≫ X.ι ≫ E.H.ι ≫ G'.hom → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ M.S), Set.range ξ = {x} → ξ ≫ b ≫ PSpace.str R E.N = s ≫ M.π → ∃ p : Sp Ω ⟶ X.toScheme, p ≫ a = ξ ∧ p ≫ X.ι ≫ E.H.ι ≫ G'.hom = s) → ∃ V : P'.Opens, x ∈ V ∧ Smooth (V.ι ≫ b ≫ PSpace.str R E.N) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (V.ι ≫ b ≫ PSpace.str R E.N) M.π := by
  intro R _ _ _ hR M G' _ _ hG E P' b X a hbsep hblft ha hsec hab hπΓ hπs x hx hx0 hinj hlift
  haveI := hbsep
  haveI := hblft
  haveI := ha
  haveI : IsProper M.π := M.proper
  haveI : IsProper (PSpace.str R E.N) := isProper_str R E.N
  have key : a ≫ b ≫ PSpace.str R E.N = X.ι ≫ E.H.ι ≫ G'.hom ≫ M.π := by
    rw [reassoc_of% hab, E.f_over]
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.Mum.exists_mem_fibre_of_geometric_lifting R M.S P' X.toScheme M.π (b ≫ PSpace.str R E.N) a (X.ι ≫ E.H.ι ≫ G'.hom) hπs x hx0 hlift
  have hz0 : M.π (G'.hom (E.H.ι (X.ι z))) = closedPoint R := by
    have h1 := congrArg (fun f : X.toScheme ⟶ Sp R => f z) key
    simp only [Scheme.Hom.comp_apply] at h1
    rw [← h1, hz]
    simpa [Scheme.Hom.comp_apply] using hx0
  obtain ⟨y, hy⟩ := (_root_.GlobalTheory.Mum.Emb.range_closed R M.S M.π G' E).1 (X.ι z) hz0
  have hyb : E.j y = b x := by
    rw [← hy, ← hz]
    have h1 := congrArg (fun f : X.toScheme ⟶ PSpace R E.N => f z) hab
    simpa [Scheme.Hom.comp_apply] using h1.symm
  obtain ⟨W0, g, τ0, O, e, hyO, hOW, hτ0, he, he2, he3⟩ := _root_.GlobalTheory.Mum.exists_etale_coords_lift_immersion R E.N E.Y E.smooth E.j E.imm E.j_over y
  have hxW1 : x ∈ b ⁻¹ᵁ W0 := by
    show b x ∈ W0
    rw [← hyb]; exact hOW hyO
  let τ1 : (b ⁻¹ᵁ W0).toScheme ⟶ 𝔸(Fin g; Sp R) := (b ∣_ W0) ≫ τ0
  have hτ1 : τ1 ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = (b ⁻¹ᵁ W0).ι ≫ b ≫ PSpace.str R E.N := by
    simp only [τ1, Category.assoc, hτ0, morphismRestrict_ι_assoc]
  let c1 : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) M.π :=
    pullback.lift ((a ∣_ (b ⁻¹ᵁ W0)) ≫ τ1) ((a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (by
      rw [Category.assoc, hτ1, morphismRestrict_ι_assoc, key]
      simp only [Category.assoc])
  have hF := _root_.GlobalTheory.Mum.fibre_etale_near R hR M G' hG E P' b X a hab x y hyb hx0 W0 g τ0 O e hyO hOW hτ0 he he2 he3 c1
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  obtain ⟨W, hWW1, hxW, hWet⟩ := _root_.GlobalTheory.exists_open_etale_restrict_of_universallyClosed X.toScheme P' _ a (b ⁻¹ᵁ W0) c1 x inferInstance hxW1 hF
  have hle : a ⁻¹ᵁ W ≤ a ⁻¹ᵁ (b ⁻¹ᵁ W0) := fun _ hp => hWW1 hp
  let c := X.toScheme.homOfLE hle ≫ c1
  let τ := P'.homOfLE hWW1 ≫ τ1
  let U : Over (Sp R) := Over.mk (W.ι ≫ b ≫ PSpace.str R E.N)
  have hsq : X.toScheme.homOfLE hle ≫ (a ∣_ (b ⁻¹ᵁ W0)) = (a ∣_ W) ≫ P'.homOfLE hWW1 := by
    rw [← cancel_mono (b ⁻¹ᵁ W0).ι, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc,
      Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]
  obtain ⟨x', hx'⟩ : x ∈ Set.range W.ι := by rw [Scheme.Opens.range_ι]; exact hxW
  have hLFT : LocallyOfFiniteType U.hom := by
    show LocallyOfFiniteType (W.ι ≫ b ≫ PSpace.str R E.N); infer_instance
  have hSep : IsSeparated U.hom := by
    show IsSeparated (W.ι ≫ b ≫ PSpace.str R E.N); infer_instance
  have hPr : IsProper (a ∣_ W) := inferInstance
  have hSec : ∀ V : U.left.Opens, Function.Bijective ((a ∣_ W).app V).hom := by
    intro V
    rw [morphismRestrict_app]
    exact (ConcreteCategory.bijective_of_isIso (X.toScheme.presheaf.map (eqToHom (image_morphismRestrict_preimage a W V)).op)).comp (hsec (W.ι ''ᵁ V))
  have hτ : τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom := by
    simp only [τ, Category.assoc, hτ1]
    rw [Scheme.homOfLE_ι_assoc]
    rfl
  have hc1 : c ≫ pullback.fst _ _ = (a ∣_ W) ≫ τ := by
    simp only [c, τ, c1, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc, hsq, Category.assoc]
  have hc2 : c ≫ pullback.snd _ _ = (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom := by
    simp only [c, c1, Category.assoc, pullback.lift_snd]
    rw [Scheme.homOfLE_ι_assoc]
  have hcl : IsClosed ({x'} : Set U.left) := by
    have : ({x'} : Set U.left) = W.ι ⁻¹' {x} := by
      ext p
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ hx', fun h => W.ι.isOpenEmbedding.injective (h.trans hx'.symm)⟩
    rw [this]
    exact hx.preimage W.ι.continuous
  have hx'0 : U.hom x' = closedPoint R := by
    show (W.ι ≫ b ≫ PSpace.str R E.N) x' = closedPoint R
    simpa [Scheme.Hom.comp_apply, hx'] using hx0
  have hrange : ∀ (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ U.left), Set.range ξ = {x'} → Set.range (ξ ≫ W.ι) = {x} := by
    intro Ω _ ξ hr
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    erw [hr]
    rw [Set.image_singleton, hx']
  have hinj' : ∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ (a ⁻¹ᵁ W).toScheme), Set.range (p ≫ (a ∣_ W)) = {x'} →
      p ≫ (a ∣_ W) = p' ≫ (a ∣_ W) → p ≫ (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom = p' ≫ (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom →
      p = p' := by
    intro Ω _ p p' hr he hb
    have hr' : Set.range ((p ≫ (a ⁻¹ᵁ W).ι) ≫ a) = {x} := by
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc]
      exact hrange Ω _ hr
    have h2 : (p ≫ (a ⁻¹ᵁ W).ι) ≫ a = (p' ≫ (a ⁻¹ᵁ W).ι) ≫ a := by
      simp only [Category.assoc, ← morphismRestrict_ι]
      rw [reassoc_of% he]
    have := hinj Ω (p ≫ (a ⁻¹ᵁ W).ι) (p' ≫ (a ⁻¹ᵁ W).ι) hr' h2 (by simpa only [Category.assoc] using hb)
    exact (cancel_mono _).1 this
  have hlift' : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ M.S), Set.range ξ = {x'} →
      ξ ≫ U.hom = s ≫ M.π → ∃ p : Sp Ω ⟶ (a ⁻¹ᵁ W).toScheme, p ≫ (a ∣_ W) = ξ ∧ p ≫ (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom = s := by
    intro Ω _ _ ξ s hr hs
    obtain ⟨p, hp1, hp2⟩ := hlift Ω (ξ ≫ W.ι) s (hrange Ω ξ hr) (by rw [Category.assoc]; exact hs)
    have hsub : Set.range p.base ⊆ Set.range (a ⁻¹ᵁ W).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      show a (p t) ∈ W
      have h3 : a (p t) = W.ι (ξ t) := by
        have h4 := congrArg (fun f : Sp Ω ⟶ P' => f t) hp1
        simpa [Scheme.Hom.comp_apply] using h4
      rw [h3]
      have h5 := Set.mem_range_self (f := W.ι) (ξ t)
      rwa [Scheme.Opens.range_ι] at h5
    refine ⟨IsOpenImmersion.lift (a ⁻¹ᵁ W).ι p hsub, ?_, ?_⟩
    · rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc, hp1]
    · rw [IsOpenImmersion.lift_fac_assoc]; exact hp2
  obtain ⟨V, hxV, hVet, hVpb⟩ := _root_.GlobalTheory.Mum.etale_coord_descend R hR M.S (a ⁻¹ᵁ W).toScheme M.π U (a ∣_ W)
    ((a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) g τ c M.proper hπs hπΓ hLFT hSep hPr hSec hτ hc1 hc2 (hWet hle)
    x' hcl hx'0 hinj' hlift'
  refine ⟨W.ι ''ᵁ V, ⟨x', hxV, hx'⟩, ?_, ?_⟩
  · haveI : Etale (V.ι ≫ τ) := hVet
    haveI : Smooth (𝔸(Fin g; Sp R) ↘ Sp R) := GlobalTheory.Mum.EtChart.affineSpace_smooth (Sp R) g
    have e1 : (W.ι ''ᵁ V).ι ≫ b ≫ PSpace.str R E.N =
        (W.ι.isoImage V).inv ≫ (V.ι ≫ τ) ≫ (𝔸(Fin g; Sp R) ↘ Sp R) := by
      rw [Category.assoc, hτ, Iso.eq_inv_comp, ← Category.assoc, Scheme.Hom.isoImage_hom_ι, Category.assoc]
      rfl
    rw [e1]
    infer_instance
  · exact _root_.GlobalTheory.isPullback_morphismRestrict_image_of_restrict_restrict P' X.toScheme M.S (Sp R) a W V (X.ι ≫ E.H.ι ≫ G'.hom) (b ≫ PSpace.str R E.N) M.π hVpb

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFinsetClosedFibreSemiAbelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_affine_open_of_finset_closedFibre :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ s : Finset G.left,
    (∀ x ∈ s, G.hom x = closedPoint R) → ∃ O : G.left.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  intro R _ _ _ hR G _ _ hG s hs
  haveI : IsNoetherianRing R := hR.1
  haveI : QuasiCompact G.hom := hG.quasiCompact
  haveI : IsSeparated G.hom := hG.separated
  haveI : Smooth G.hom := hG.smooth
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom

  rcases s.eq_empty_or_nonempty with hs0 | ⟨x₀, hx₀⟩
  · exact ⟨⊥, isAffineOpen_bot _, by simp [hs0]⟩

  have hcl : ∀ x : G.left, ∃ y ∈ closure ({x} : Set G.left), IsClosed ({y} : Set G.left) :=
    fun x => isClosed_closure.exists_closed_singleton ⟨x, subset_closure rfl⟩
  choose f hfx hfc using hcl
  have hsp : ∀ x, x ⤳ f x := fun x => specializes_iff_mem_closure.2 (hfx x)
  have hcp : IsClosed ({closedPoint R} : Set (Sp R)) := isClosed_singleton_closedPoint R
  have hfib : ∀ x ∈ s, G.hom (f x) = closedPoint R := by
    intro x hx
    have h1 : G.hom x ⤳ G.hom (f x) := (hsp x).map G.hom.continuous
    rw [hs x hx] at h1
    have h2 := specializes_iff_mem_closure.1 h1
    exact closure_minimal (subset_refl _) hcp h2
  classical
  let s' : Finset G.left := s.image f
  have hs' : ∀ y ∈ s', G.hom y = closedPoint R ∧ IsClosed ({y} : Set G.left) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨hfib x hx, hfc x⟩
  suffices H : ∃ O : G.left.Opens, IsAffineOpen O ∧ ∀ y ∈ s', y ∈ O by
    obtain ⟨O, hO, hyO⟩ := H
    exact ⟨O, hO, fun x hx => (hsp x).mem_open O.2 (hyO _ (Finset.mem_image_of_mem f hx))⟩

  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens)
    (show x₀ ∈ (⊤ : G.left.Opens) from trivial)

  obtain ⟨O, ⟨u, huO, hu⟩, hmove⟩ :=
    _root_.GlobalTheory.Mum.exists_open_mul_mem R G hG V ⟨x₀, hxV, hs x₀ hx₀⟩ s' hs'

  obtain ⟨R₁, _, _, _, ρ, a, hfin, het, ha, haO⟩ :=
    _root_.GlobalTheory.Mum.exists_finEtale_section_of_smooth R hR G hG.smooth O ⟨u, huO, hu⟩
  letI : Algebra R R₁ := ρ.toAlgebra
  haveI : Module.Finite R R₁ := hfin.2.2
  haveI : Algebra.Etale R R₁ := het
  haveI : Module.Flat R R₁ := inferInstance
  haveI : Module.Free R R₁ := Module.free_of_flat_of_isLocalRing

  let A : Over.mk (spMap ρ) ⟶ G := Over.homMk a ha
  obtain ⟨W, hW, hzW⟩ := _root_.GlobalTheory.Mum.translate_baseChange_affineOpen R R₁ ρ G V hV A

  have hpb : IsPullback (pullback.fst G.hom (spMap ρ)) (pullback.snd G.hom (spMap ρ)) G.hom
      (spMap (algebraMap R R₁)) := IsPullback.of_hasPullback G.hom (spMap ρ)
  refine _root_.GlobalTheory.Mum.exists_isAffineOpen_of_preimage_le_affine R R₁ G.left (pullback G.hom (spMap ρ)) G.hom (pullback.snd _ _) (pullback.fst _ _)
    hpb inferInstance inferInstance W hW s' ?_
  intro z hz
  let Ω := (pullback G.hom (spMap ρ)).residueField z
  let z' : Sp Ω ⟶ pullback G.hom (spMap ρ) := (pullback G.hom (spMap ρ)).fromSpecResidueField z
  have hz' : ∀ w, z' w = z := fun w => Scheme.fromSpecResidueField_apply z w
  let t : Sp Ω ⟶ Sp R := z' ≫ pullback.fst _ _ ≫ G.hom
  let x : Over.mk t ⟶ G := Over.homMk (z' ≫ pullback.fst _ _) (by simp [t])
  let a' : Over.mk t ⟶ G := Over.homMk (z' ≫ pullback.snd _ _ ≫ a)
    (by simp only [t, Over.mk_hom, Category.assoc, ha, pullback.condition])
  have hx : ∀ w, x.left w ∈ s' := by
    intro w
    show (z' ≫ pullback.fst _ _) w ∈ s'
    rw [Scheme.Hom.comp_apply, hz']
    exact hz
  have ha' : ∀ w, a'.left w ∈ O := by
    intro w
    show (z' ≫ pullback.snd _ _ ≫ a) w ∈ O
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact haO ⟨_, rfl⟩
  have hV' := hmove Ω t x a' hx ha'
  have := hzW Ω z' t x a' rfl rfl hV' (closedPoint Ω)
  first
    | exact (Scheme.fromSpecResidueField_apply z _) ▸ this
    | simpa only [hz'] using this
    | (convert this using 1; exact (hz' _).symm)

end GlobalTheory.Mum
end

