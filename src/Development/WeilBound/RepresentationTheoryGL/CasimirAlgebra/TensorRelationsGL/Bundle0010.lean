module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle0006

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSWStartB
section
noncomputable section

open Formalism.REAL Matrix MeasureTheory

namespace PositivityTheory.Rg.Cz

namespace SWS

variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
  {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}

theorem dense [CompactSpace Γ] [T2Space Γ] (hK : IsKD bar κ) {H : Set ι} (hH : ∀ τ, τ ∈ H ↔ bar τ ∉ H)
    (g : C(Γ, ℂ)) : g ∈ closure {h : C(Γ, ℂ) | ⇑h ∈ Submodule.span ℂ (Mono κ H)} := by
  let S : Set C(Γ, ℂ) := {g | ∃ τ i j, (g : Γ → ℂ) = fun k => κ τ k i j}
  let A : StarSubalgebra ℂ C(Γ, ℂ) := StarAlgebra.adjoin ℂ S
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨τ, hτ⟩ : ∃ τ, κ τ x ≠ κ τ y := by
      by_contra h
      push Not at h
      exact hxy (hK.sep x y h)
    obtain ⟨i, j, hij⟩ : ∃ i j, κ τ x i j ≠ κ τ y i j := by
      by_contra h
      push Not at h
      exact hτ (Matrix.ext h)
    exact ⟨fun k => κ τ k i j, ⟨⟨fun k => κ τ k i j, hK.cont τ i j⟩,
      StarAlgebra.subset_adjoin ℂ S ⟨τ, i, j, rfl⟩, rfl⟩, hij⟩
  have hsub : A.toSubalgebra ≤ (monoAlg hK H).comap (ContinuousMap.coeFnAlgHom ℂ) := by
    rw [StarAlgebra.adjoin_toSubalgebra]
    apply Algebra.adjoin_le
    rintro g (hg | hg)
    · obtain ⟨τ, i, j, hg⟩ := hg
      show (g : Γ → ℂ) ∈ Submodule.span ℂ (Mono κ H)
      rw [hg]
      exact entry_mem hK hH τ i j
    · obtain ⟨τ, i, j, hg⟩ := Set.mem_star.1 hg
      show (g : Γ → ℂ) ∈ Submodule.span ℂ (Mono κ H)
      have : (g : Γ → ℂ) = fun k => κ (bar τ) k i j := by
        funext k
        have h1 := congrFun hg k
        simp only [ContinuousMap.star_apply] at h1
        rw [hK.conj, ← h1, star_star]
      rw [this]
      exact entry_mem hK hH (bar τ) i j
  have hle : ∀ h ∈ A, ⇑h ∈ Submodule.span ℂ (Mono κ H) := fun h hh => hsub hh
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have hg : g ∈ A.topologicalClosure := by rw [htop]; exact StarSubalgebra.mem_top
  rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe] at hg
  exact closure_mono (fun h hh => hle h hh) hg

theorem nonvanish [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] [T2Space Γ] (μ : Measure Γ) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (hK : IsKD bar κ) {H : Set ι} (hH : ∀ τ, τ ∈ H ↔ bar τ ∉ H)
    {f : Γ → ℂ} (hf : Continuous f) (x : Γ) (hx : f x ≠ 0) : ∃ g ∈ Mono κ H, ∫ k, g k * f k ∂μ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hspan : ∀ g ∈ Submodule.span ℂ (Mono κ H), Continuous g ∧ ∫ k, g k * f k ∂μ = 0 := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      refine ⟨?_, hcon g hg⟩
      obtain ⟨m, lab, c, I, K, -, rfl⟩ := hg
      exact mono_cont hK lab c I K
    | zero => exact ⟨continuous_const, by simp⟩
    | add g g' _ _ h h' =>
      refine ⟨h.1.add h'.1, ?_⟩
      simp only [Pi.add_apply, add_mul]
      rw [integral_add (integrable_of_cont μ (f := fun k => g k * f k) (h.1.mul hf))
        (integrable_of_cont μ (f := fun k => g' k * f k) (h'.1.mul hf)), h.2, h'.2,
        add_zero]
    | smul a g _ h =>
      refine ⟨h.1.const_smul a, ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, h.2, mul_zero]
  let F : C(Γ, ℂ) := ⟨fun k => star (f k), hf.star⟩
  let f' : C(Γ, ℂ) := ⟨f, hf⟩
  have hclose := dense hK hH F
  have hbound : ∀ ε > 0, ‖∫ k, F k * f k ∂μ‖ ≤ ε * (‖f'‖ * μ.real Set.univ) := by
    intro ε hε
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hclose ε hε
    have hb' := hspan b hb
    have heq : ∫ k, F k * f k ∂μ = ∫ k, (F k - b k) * f k ∂μ := by
      rw [← sub_zero (∫ k, F k * f k ∂μ), ← hb'.2, ← integral_sub
        (integrable_of_cont μ (f := fun k => F k * f k) (F.continuous.mul hf))
        (integrable_of_cont μ (f := fun k => b k * f k) (b.continuous.mul hf))]
      congr 1
      funext k
      ring
    rw [heq, ← mul_assoc]
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k => ?_)
    rw [norm_mul]
    have h1 : ‖F k - b k‖ ≤ ε := by
      have := ContinuousMap.norm_coe_le_norm (F - b) k
      rw [dist_eq_norm] at hdist
      simp only [ContinuousMap.sub_apply] at this
      linarith
    have h2 : ‖f k‖ ≤ ‖f'‖ := ContinuousMap.norm_coe_le_norm f' k
    exact mul_le_mul h1 h2 (norm_nonneg _) hε.le
  have hzero : ∫ k, F k * f k ∂μ = 0 := by
    by_contra hne
    have hpos : 0 < ‖∫ k, F k * f k ∂μ‖ := norm_pos_iff.2 hne
    set C := ‖f'‖ * μ.real Set.univ
    have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) measureReal_nonneg
    set x := ‖∫ k, F k * f k ∂μ‖
    have := hbound (x / (2 * (C + 1))) (by positivity)
    have h3 : x / (2 * (C + 1)) * C ≤ x / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hre : ∀ k, F k * f k = ((‖f k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    simp only [F, ContinuousMap.coe_mk]
    rw [Complex.ofReal_pow]
    exact RCLike.conj_mul (f k)
  simp_rw [hre, integral_complex_ofReal, Complex.ofReal_eq_zero] at hzero
  have hint : Integrable (fun k => ‖f k‖ ^ 2) μ := by
    have := (integrable_of_cont μ (f := fun k => ((‖f k‖ ^ 2 : ℝ) : ℂ)) (by fun_prop)).re
    exact this
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => sq_nonneg ‖f k‖) hint).1 hzero
  have hfun := (Continuous.ae_eq_iff_eq μ (by fun_prop) continuous_const).1 hae
  have h0 : ‖f x‖ ^ 2 = 0 := congrFun hfun x
  exact hx (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0))

end SWS

end PositivityTheory.Rg.Cz

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PStepFormula
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace PStepFormula

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem one (hT : TensorGl) (hJ : JMComm) (hQ : PiQdet) (hC : Curry) (E : Fin n → Fin n → Module.End ℂ M)
    (hE : GlRel E) (u : ℂ) :
    (PiJ 1 E u * qdet (tE (Finset.univ : Finset (Fin 1)) E) u : Module.End ℂ (TV n M (Fin 1))) =
      lift (qdet E u) * PiJ 1 E (u + 1) := by
  obtain ⟨hbij, -, h3, h4, -, -, h7⟩ := hC n M E 1 n
  set e := LinearEquiv.ofBijective (curF n M 1 n) hbij
  have hG : GlRel (tE (Finset.univ : Finset (Fin 1)) E) := (hT n M (Fin 1) E hE Finset.univ).1
  have hE' : GlRel (fun a b => (lift (E a b) : Module.End ℂ (TV n M (Fin 1)))) :=
    glRel_map (liftA n M (Fin 1)) hE
  have hsw : ∀ a b : Fin n, e.conjAlgEquiv ℂ (pm (Equiv.swap (Fin.natAdd 1 a) (Fin.natAdd 1 b))) =
      pm (Equiv.swap a b) := fun a b => conj_eq e fun x => LinearMap.congr_fun (h7 a b) x
  have hOr : ∀ j : Fin n, e.conjAlgEquiv ℂ (Om E (Fin.natAdd 1 j)) = Om (fun a b => lift (E a b)) j :=
    fun j => conj_eq e fun x => curF_Om_r E j x
  have hOl : e.conjAlgEquiv ℂ (Om E (Fin.castAdd n (0 : Fin 1))) = lift (Om E 0) :=
    conj_eq e fun x => curF_Om_l E 0 x
  have s1 : e.conjAlgEquiv ℂ (PiJ (1 + n) E u) = lift (PiJ 1 E u) * PiJ n (tE Finset.univ E) u := by
    rw [lift_PiJ]
    unfold PiJ
    rw [List.ofFn_add, List.prod_append, map_mul, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    simp only [Function.comp_def, map_add (f := _), AlgEquiv.commutes]
    congr 2
    · congr 1; funext i; congr 1; exact conj_eq e fun x => LinearMap.congr_fun (h3 i) x
    · congr 1; funext j; congr 1; exact conj_eq e fun x => LinearMap.congr_fun (h4 j) x
  set Q : Module.End ℂ (TV n M (Fin (1 + n))) :=
    ∑ j : Fin n, pm (Equiv.swap (Fin.natAdd 1 j) (Fin.castAdd n 0)) with hQdef
  have s2 : e.conjAlgEquiv ℂ (PiJ (1 + n) E u) =
      PiJ n (fun a b => lift (E a b)) u * (algebraMap ℂ _ u + lift (Om E 0) + e.conjAlgEquiv ℂ Q) := by
    have hR : pm (rot n) * PiJ (1 + n) E u * pm (rot n)⁻¹ = PiJ (1 + n) E u := by
      rw [← ((hJ n M E hE (1 + n)).2.2 u (rot n)).eq, mul_assoc, ← pm_mul, mul_inv_cancel, pm_one, mul_one]
    let eρ : TV n M (Fin (1 + n)) ≃ₗ[ℂ] TV n M (Fin (1 + n)) :=
      LinearEquiv.ofLinear (pm (rot n)) (pm (rot n)⁻¹)
        (by rw [← Module.End.mul_eq_comp, ← pm_mul, mul_inv_cancel, pm_one]; rfl)
        (by rw [← Module.End.mul_eq_comp, ← pm_mul, inv_mul_cancel, pm_one]; rfl)
    have hΨ : ∀ T, eρ.conjAlgEquiv ℂ T = pm (rot n) * T * pm (rot n)⁻¹ := fun T => rfl
    rw [← hR, ← hΨ]
    unfold PiJ
    rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn, List.ofFn_congr (Nat.add_comm 1 n),
      List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
    simp only [Function.comp_apply, map_add (f := _), AlgEquiv.commutes]
    congr 1
    · congr 1; congr 1; funext j; congr 1
      have hk : (Fin.cast (Nat.add_comm 1 n).symm j.castSucc : Fin (1 + n)) = ⟨j, by omega⟩ := Fin.ext (by simp)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hΨ, conj_xJ hT E hE, hk, rot_nat, map_add (f := _), hOr, xJ, sum_lt_cast _ (by simp), map_sum]
      congr 1
      refine Finset.sum_congr (Finset.filter_congr fun i _ => Iff.rfl) fun i _ => ?_
      rw [rot_nat, hsw]
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [hΨ, conj_xJ hT E hE, rot_last _ (by simp), map_add (f := _), hOl, sum_lt_cast _ (by simp), hQdef, map_sum, map_sum,
          add_assoc]
      congr 2
      refine Finset.sum_congr (Finset.filter_true_of_mem fun i _ => by simp) fun i _ => ?_
      rw [rot_nat]
  have hQalt : e.conjAlgEquiv ℂ Q * alt Finset.univ = alt Finset.univ := by
    apply LinearMap.ext; intro g
    rw [Module.End.mul_apply]
    funext J I
    have hsymm : ∀ (y : TV n (TV n M (Fin 1)) (Fin n)) (I' : Fin 1 → Fin n) (J' : Fin n → Fin n),
        e.symm y (Fin.append I' J') = y J' I' := fun y I' J' =>
      congrFun (congrFun (e.apply_symm_apply y) J') I'
    show (Q (e.symm (alt Finset.univ g))) (Fin.append I J) = _
    rw [hQdef, LinearMap.sum_apply, Finset.sum_apply]
    simp only [pm_apply, app_swap, hsymm]
    exact sum_swap (fun J I => alt Finset.univ g J I) (fun J a b hab => alt_swap g J a b hab) J I
  have hq1 := hQ n _ _ hG u
  have hq2 := hQ n _ _ hE' u
  have hqE : qdet (fun a b => (lift (E a b) : Module.End ℂ (TV n M (Fin 1)))) u = lift (qdet E u) :=
    (qdet_map (liftA n M (Fin 1)) E u).symm
  have hcomm : ∀ B : Module.End ℂ (TV n M (Fin 1)),
      (alt Finset.univ : Module.End ℂ (TV n (TV n M (Fin 1)) (Fin n))) * lift B = lift B * alt Finset.univ := by
    intro B
    simp only [alt, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, (lift_comm_pm B _).eq]
  have hl : (lift (algebraMap ℂ _ (u + 1) + Om E 0) : Module.End ℂ (TV n (TV n M (Fin 1)) (Fin n))) =
      algebraMap ℂ _ u + lift (Om E 0) + 1 := by
    rw [← liftA_apply, map_add (f := _), AlgHom.commutes, liftA_apply, map_add (f := _), map_one]; abel
  rw [PiJ_one E (u + 1)]
  apply ext_of_alt (n := n)
  calc lift (PiJ 1 E u * qdet (tE Finset.univ E) u) * alt Finset.univ
      = lift (PiJ 1 E u) * (PiJ n (tE Finset.univ E) u * alt Finset.univ) := by rw [hq1, lift_mul, mul_assoc]
    _ = e.conjAlgEquiv ℂ (PiJ (1 + n) E u) * alt Finset.univ := by rw [s1, mul_assoc]
    _ = PiJ n (fun a b => lift (E a b)) u * (lift (algebraMap ℂ _ (u + 1) + Om E 0) * alt Finset.univ) := by
        rw [s2, mul_assoc, hl, add_mul, hQalt, add_mul _ 1, one_mul]
    _ = PiJ n (fun a b => lift (E a b)) u * alt Finset.univ * lift (algebraMap ℂ _ (u + 1) + Om E 0) := by
        rw [← hcomm, mul_assoc]
    _ = lift (lift (qdet E u) * (algebraMap ℂ _ (u + 1) + Om E 0)) * alt Finset.univ := by
        rw [hq2, hqE, mul_assoc, hcomm, ← mul_assoc, ← lift_mul]

end PStepFormula

open PStepFormula in
theorem stepFormula_of : TensorGl → JMComm → PiQdet → Curry → StepFormula := by
  intro hT hJ hQ hC n M _ _ E hE m
  induction m generalizing M with
  | zero =>
    intro u
    have h0 : (tE (Finset.univ : Finset (Fin 0)) E : Fin n → Fin n → Module.End ℂ (TV n M (Fin 0))) =
        fun a b => liftA n M (Fin 0) (E a b) := by
      funext a b; simp [tE, liftA_apply]
    rw [h0, ← qdet_map, liftA_apply]
    simp [PiJ]
  | succ m ih =>
    intro u
    obtain ⟨hbij, h2, h3, h4, h5, -, -⟩ := hC n M E m 1
    set e := LinearEquiv.ofBijective (curF n M m 1) hbij
    have hG : GlRel (tE (Finset.univ : Finset (Fin m)) E) := (hT n M (Fin m) E hE Finset.univ).1
    have hsplit : ∀ v : ℂ, e.conjAlgEquiv ℂ (PiJ (m + 1) E v) =
        lift (PiJ m E v) * PiJ 1 (tE Finset.univ E) v := by
      intro v
      rw [lift_PiJ]
      unfold PiJ
      rw [List.ofFn_add, List.prod_append, map_mul, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
      simp only [Function.comp_def, map_add (f := _), AlgEquiv.commutes]
      congr 2
      · congr 1; funext i; congr 1; exact conj_eq e fun x => LinearMap.congr_fun (h3 i) x
      · congr 1; funext j; congr 1; exact conj_eq e fun x => LinearMap.congr_fun (h4 j) x
    have hq : e.conjAlgEquiv ℂ (qdet (tE (Finset.univ : Finset (Fin (m + 1))) E) u) =
        qdet (tE (Finset.univ : Finset (Fin 1)) (tE (Finset.univ : Finset (Fin m)) E)) u := by
      rw [← AlgEquiv.coe_toAlgHom, qdet_map]
      congr 1; funext a b
      exact conj_eq e fun x => LinearMap.congr_fun (h2 a b) x
    have hl : e.conjAlgEquiv ℂ (lift (qdet E u)) = lift (lift (qdet E u)) :=
      conj_eq e fun x => LinearMap.congr_fun (h5 _) x
    apply (e.conjAlgEquiv ℂ).injective
    rw [map_mul, map_mul, hsplit, hsplit, hq, hl, mul_assoc, one hT hJ hQ hC _ hG, ← mul_assoc, ← lift_mul, ih M E hE,
      lift_mul, mul_assoc]

end PositivityTheory.Rg.Cz

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransAllB
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TA

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  (q : P → Prop) [DecidablePred q]

def merge (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) : P → Fin n :=
  fun p => if h : q p then J ⟨p, h⟩ else I ⟨p, h⟩

omit [Fintype P] [DecidableEq P] in
theorem merge_left (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // q p}) :
    merge q J I x.1 = J x := by simp [merge, x.2]

omit [Fintype P] [DecidableEq P] in
theorem merge_right (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // ¬ q p}) :
    merge q J I x.1 = I x := by simp [merge, x.2]

omit [Fintype P] in
theorem merge_upd_left (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // q p}) (c : Fin n) :
    merge q (Function.update J x c) I = Function.update (merge q J I) x.1 c := by
  funext p
  by_cases h : q p
  · by_cases hp : p = x.1
    · subst hp
      simp [merge, h]
    · have hx : (⟨p, h⟩ : {p // q p}) ≠ x := fun e => hp (congrArg Subtype.val e)
      simp [merge, h, hp, Function.update_of_ne hx]
  · have hp : p ≠ x.1 := fun e => h (e ▸ x.2)
    simp [merge, h, hp]

omit [Fintype P] in
theorem merge_upd_right (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // ¬ q p}) (c : Fin n) :
    merge q J (Function.update I x c) = Function.update (merge q J I) x.1 c := by
  funext p
  by_cases h : q p
  · have hp : p ≠ x.1 := fun e => x.2 (e ▸ h)
    simp [merge, h, hp]
  · by_cases hp : p = x.1
    · subst hp
      simp [merge, h]
    · have hx : (⟨p, h⟩ : {p // ¬ q p}) ≠ x := fun e => hp (congrArg Subtype.val e)
      simp [merge, h, hp, Function.update_of_ne hx]

def spl : TV n M P ≃ₗ[ℂ] TV n (TV n M {p // ¬ q p}) {p // q p} where
  toFun F J I := F (merge q J I)
  invFun G K := G (fun x => K x.1) (fun x => K x.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv F := by
    funext K
    show F (merge q _ _) = F K
    congr 1
    funext p
    by_cases h : q p <;> simp [merge, h]
  right_inv G := by
    funext J I
    show G (fun x => merge q J I x.1) (fun x => merge q J I x.1) = G J I
    congr 1 <;> funext x
    · exact merge_left q J I x
    · exact merge_right q J I x

omit [Fintype P] [DecidableEq P] in
theorem spl_apply (F : TV n M P) (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) :
    spl q F J I = F (merge q J I) := rfl

omit [Fintype P] in
theorem spl_tE (S : Finset P) (F : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : TV n M P) :
    spl q (tE S F a b f) =
      tE (S.subtype q) (fun a b => tE (S.subtype fun p => ¬ q p) F a b) a b (spl q f) := by
  funext J I
  simp only [spl_apply, tE, lift, eAt, LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Pi.add_apply]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not S q, add_comm]
  congr 1
  · rw [← Finset.sum_subtype_eq_sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : I x = a
    · simp [h, merge_right, spl_apply, merge_upd_right]
    · simp [h, merge_right]
  · rw [← Finset.sum_subtype_eq_sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : J x = a
    · simp [h, merge_left, spl_apply, merge_upd_left]
    · simp [h, merge_left]

omit [DecidableEq P] in
theorem card_sub (r : P → Prop) [DecidablePred r] :
    (Finset.univ.filter fun x : {p // q p} => r x.1).card = (Finset.univ.filter fun p => q p ∧ r p).card := by
  rw [← Finset.card_map (Function.Embedding.subtype q)]
  congr 1
  ext p
  simp [and_comm]

private theorem subtypePerm_subtypeCongr_eq {q : P → Prop} [DecidablePred q] (σ : Equiv.Perm P)
    (h0 : ∀ x, q (σ x) ↔ q x) (h1 : ∀ x, ¬ q (σ x) ↔ ¬ q x) :
    (σ.subtypePerm h0).subtypeCongr (σ.subtypePerm (p := fun x => ¬ q x) h1) = σ := by
  ext x
  by_cases hx : q x
  · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hx]
    rfl
  · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hx]
    rfl

theorem cA_split {C : Type} [DecidableEq C] (col : P → C) (hq : ∀ p p', col p = col p' → (q p ↔ q p'))
    (b : P → Fin n) (F : TV n M P) :
    cA col b F = cA (fun x : {p // ¬ q p} => col x.1) (fun x => b x.1)
      (cA (fun x : {p // q p} => col x.1) (fun x => b x.1) (spl q F)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cA, alt, colG, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, map_sum, map_smul, pm, LinearMap.pi_apply]
  simp_rw [Finset.smul_sum, smul_smul, spl_apply]
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun τ _ => τ.1.subtypeCongr τ.2) ?_ ?_ ?_ ?_
  · rintro ⟨σ0, σ1⟩ hτ
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    intro x
    by_cases hx : q x
    · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hx]
      exact hτ.1 ⟨x, hx⟩
    · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hx]
      exact hτ.2 ⟨x, hx⟩
  · rintro ⟨σ0, σ1⟩ _ ⟨σ0', σ1'⟩ _ he
    simp only at he
    have e0 : σ0 = σ0' := by
      ext x
      have := congrArg (fun σ : Equiv.Perm P => σ x.1) he
      simp only [Equiv.Perm.subtypeCongr.left_apply _ _ x.2] at this
      exact this
    have e1 : σ1 = σ1' := by
      ext x
      have := congrArg (fun σ : Equiv.Perm P => σ x.1) he
      simp only [Equiv.Perm.subtypeCongr.right_apply _ _ x.2] at this
      exact this
    rw [e0, e1]
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    have h0 : ∀ x, q (σ x) ↔ q x := fun x => hq _ _ (hσ x)
    have h1 : ∀ x, ¬ q (σ x) ↔ ¬ q x := fun x => not_congr (h0 x)
    refine ⟨(σ.subtypePerm h0, σ.subtypePerm (p := fun x => ¬ q x) h1), ?_, subtypePerm_subtypeCongr_eq σ h0 h1⟩
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun x => hσ x.1, fun x => hσ x.1⟩
  · rintro ⟨σ0, σ1⟩ _
    simp only
    rw [Equiv.Perm.sign_subtypeCongr]
    congr 1
    · push_cast
      ring
    · congr 1
      funext x
      by_cases hx : q x
      · simp [merge, hx, Equiv.Perm.subtypeCongr.left_apply _ _ hx]
      · simp [merge, hx, Equiv.Perm.subtypeCongr.right_apply _ _ hx]

end PositivityTheory.Rg.Cz.TA

end
end

