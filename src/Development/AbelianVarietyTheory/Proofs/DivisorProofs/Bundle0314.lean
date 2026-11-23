module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsuppMapDomainEqZeroAtFilteredStage
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem filtered_identify_pairs {J : Type} [SmallCategory J] [IsFiltered J] (P : J ⥤ Type)
    (Q : Type) (ι : ∀ j, P.obj j → Q)
    (hinj : ∀ j (x y : P.obj j), ι j x = ι j y → ∃ (k : J) (f : j ⟶ k), P.map f x = P.map f y)
    (j : J) (T : Finset (P.obj j × P.obj j)) (hT : ∀ p ∈ T, ι j p.1 = ι j p.2) :
    ∃ (k : J) (f : j ⟶ k), ∀ p ∈ T, P.map f p.1 = P.map f p.2 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨j, 𝟙 j, by simp⟩
  | @insert p T hp ih =>
    obtain ⟨k1, f1, h1⟩ := ih (fun q hq => hT q (Finset.mem_insert_of_mem hq))
    obtain ⟨k2, f2, h2⟩ := hinj j p.1 p.2 (hT p (Finset.mem_insert_self p T))
    have e : f1 ≫ IsFiltered.leftToMax k1 k2 ≫
          IsFiltered.coeqHom (f1 ≫ IsFiltered.leftToMax k1 k2) (f2 ≫ IsFiltered.rightToMax k1 k2) =
        f2 ≫ IsFiltered.rightToMax k1 k2 ≫
          IsFiltered.coeqHom (f1 ≫ IsFiltered.leftToMax k1 k2) (f2 ≫ IsFiltered.rightToMax k1 k2) := by
      simpa only [Category.assoc] using
        IsFiltered.coeq_condition (f1 ≫ IsFiltered.leftToMax k1 k2) (f2 ≫ IsFiltered.rightToMax k1 k2)
    refine ⟨_, f1 ≫ IsFiltered.leftToMax k1 k2 ≫
          IsFiltered.coeqHom (f1 ≫ IsFiltered.leftToMax k1 k2) (f2 ≫ IsFiltered.rightToMax k1 k2), ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · rw [e]
      simp only [Functor.map_comp_apply, h2]
    · simp only [Functor.map_comp_apply, h1 q hq]

theorem finsupp_mapDomain_eq_zero_at_stage (Λ : Type 1) [AddCommGroup Λ] (J : Type)
    [SmallCategory J] [IsFiltered J] (P : J ⥤ Type) (Q : Type) (ι : ∀ j, P.obj j → Q)
    (hcompat : ∀ (j k : J) (f : j ⟶ k) (x : P.obj j), ι k (P.map f x) = ι j x)
    (hinj : ∀ j (x y : P.obj j), ι j x = ι j y → ∃ (k : J) (f : j ⟶ k), P.map f x = P.map f y)
    (j : J) (x : P.obj j →₀ Λ) (hx : Finsupp.mapDomain (ι j) x = 0) :
    ∃ (k : J) (f : j ⟶ k), Finsupp.mapDomain (P.map f) x = 0 := by
  classical
  obtain ⟨k, f, hf⟩ := filtered_identify_pairs P Q ι hinj j
    ((x.support ×ˢ x.support).filter (fun p => ι j p.1 = ι j p.2))
    (fun p hp => (Finset.mem_filter.mp hp).2)
  refine ⟨k, f, ?_⟩
  have hcomp : Finsupp.mapDomain (ι k) (Finsupp.mapDomain (P.map f) x) =
      Finsupp.mapDomain (ι j) x := by
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext a
    exact hcompat j k f a
  have hInj : Set.InjOn (ι k) (P.map f '' (x.support : Set (P.obj j))) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [hcompat, hcompat] at hab
    exact hf (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩)
  apply Finsupp.mapDomain_injOn _ hInj
  · intro b hb
    have := Finsupp.mapDomain_support (f := P.map f) (s := x) hb
    simpa using this
  · simp
  · rw [hcomp, hx, Finsupp.mapDomain_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagColumnUnipotentMemPeriodUnipotentIntegralGL
section
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

namespace GlobalTheory.DiagVol

theorem colE_mem_symN_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (t : n ⊕ Fin c) (y : n ⊕ Fin c → k) (hy : ∀ r, y r ∈ 𝒪[k])
    (hz : ∀ r, ¬ ordL c r < ordL c t → y r = 0) :
    ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c),
      x.val = 1 + Matrix.of (fun r s => if s = t then y r else 0) := by
  set E : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k := Matrix.of (fun r s => if s = t then y r else 0) with hE
  have hyt : y t = 0 := hz t (lt_irrefl _)
  have hEE : E * E = 0 := by
    ext r s
    simp only [hE, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    rw [Finset.sum_eq_single t]
    · simp [hyt]
    · intro u _ hu; simp [hu]
    · intro h; exact absurd (Finset.mem_univ t) h
  have h1 : (1 + E) * (1 - E) = 1 := by
    have : (1 + E) * (1 - E) = 1 - E * E := by noncomm_ring
    rw [this, hEE, sub_zero]
  have h2 : (1 - E) * (1 + E) = 1 := by
    have : (1 - E) * (1 + E) = 1 - E * E := by noncomm_ring
    rw [this, hEE, sub_zero]
  let x : GL (n ⊕ Fin c) k := ⟨1 + E, 1 - E, h1, h2⟩
  have hone : ∀ i j : n ⊕ Fin c, (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hEi : ∀ i j, E i j ∈ 𝒪[k] := by
    intro i j
    simp only [hE, Matrix.of_apply]
    split_ifs
    · exact hy i
    · exact zero_mem _
  have hInN : ∀ p : ℕ, (∀ r, y r ≠ 0 → lev p r < lev (n := n) (c := c) p t) → InN p x := by
    intro p hp r s hrs
    show (1 + E) r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s
    rw [Matrix.add_apply, add_eq_left]
    simp only [hE, Matrix.of_apply]
    split_ifs with h
    · subst h
      by_contra hne
      exact absurd hrs (not_le.2 (hp r hne))
    · rfl
  refine ⟨x, Subgroup.mem_inf.2 ⟨?_, ?_⟩, rfl⟩
  · show x ∈ N k n c ((c + 1) / 2) ⊔ N k n c (c / 2 + 1)
    cases t with
    | inr j =>
      refine Subgroup.mem_sup_left (Model.mem_N_iff.2 (hInN _ fun r hr => ?_))
      have hlt : ordL c r < ordL c (Sum.inr j : n ⊕ Fin c) := by
        by_contra h; exact hr (hz r h)
      cases r with
      | inl a => simp [ordL, lev] at hlt ⊢; omega
      | inr i => simp [ordL, lev] at hlt ⊢; omega
    | inl a0 =>
      refine Subgroup.mem_sup_right (Model.mem_N_iff.2 (hInN _ fun r hr => ?_))
      have hlt : ordL c r < ordL c (Sum.inl a0 : n ⊕ Fin c) := by
        by_contra h; exact hr (hz r h)
      cases r with
      | inl a => simp [ordL, lev] at hlt ⊢
      | inr i => simp [ordL, lev] at hlt ⊢; omega
  · refine (mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · show (1 + E) i j ∈ 𝒪[k]
      rw [Matrix.add_apply]; exact add_mem (hone i j) (hEi i j)
    · show (1 - E) i j ∈ 𝒪[k]
      rw [Matrix.sub_apply]; exact sub_mem (hone i j) (hEi i j)

end GlobalTheory.DiagVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagGramDensityInequalityComplex
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.FlagGram

theorem cube_cbrt (t : ℝ) (ht : 0 ≤ t) : (t ^ (1/3:ℝ)) ^ 3 = t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]; norm_num

theorem rpow_neg_four_thirds (t : ℝ) (ht : 0 ≤ t) :
    t ^ (-(4/3:ℝ)) = ((t ^ (1/3:ℝ)) ^ 4)⁻¹ := by
  rw [Real.rpow_neg ht, ← Real.rpow_natCast, ← Real.rpow_mul ht]; norm_num

theorem sq_mul_le_cubes (a w : ℝ) (ha : 1 ≤ a) (hw : 1 ≤ w) :
    a ^ 2 * w ≤ a ^ 3 + w ^ 3 - 1 := by
  have ha3 : 1 ≤ a ^ 3 := one_le_pow₀ ha
  have hw3 : 1 ≤ w ^ 3 := one_le_pow₀ hw
  rcases le_total a w with h | h
  · nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ w) (sub_nonneg.2 h)) (by linarith : (0:ℝ) ≤ w + a)]
  · nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.2 h)]

theorem key (A B C D : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hBD : B ≤ D) :
    ((1 + A + B) ^ 2 * (1 + C + D) ^ 2)⁻¹ ≤
      (1 + A) ^ (-(4 / 3 : ℝ)) * (1 + C) ^ (-(4 / 3 : ℝ)) *
        ((1 + B) ^ (-(4 / 3 : ℝ)) + (1 + D) ^ (-(4 / 3 : ℝ))) := by
  rw [rpow_neg_four_thirds _ (by linarith), rpow_neg_four_thirds _ (by linarith),
    rpow_neg_four_thirds _ (by linarith), rpow_neg_four_thirds _ (by linarith)]
  have eA := cube_cbrt (1 + A) (by linarith)
  have eB := cube_cbrt (1 + B) (by linarith)
  have eC := cube_cbrt (1 + C) (by linarith)
  have hα : 1 ≤ (1 + A) ^ (1/3:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hβ : 1 ≤ (1 + B) ^ (1/3:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hγ : 1 ≤ (1 + C) ^ (1/3:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hδ : 0 < (1 + D) ^ (1/3:ℝ) := Real.rpow_pos_of_pos (by linarith) _
  generalize (1 + A) ^ (1/3:ℝ) = α at *
  generalize (1 + B) ^ (1/3:ℝ) = β at *
  generalize (1 + C) ^ (1/3:ℝ) = γ at *
  generalize (1 + D) ^ (1/3:ℝ) = δ at *
  have hx : α ^ 2 * β ≤ 1 + A + B := by have := sq_mul_le_cubes α β hα hβ; linarith
  have hy : γ ^ 2 * β ≤ 1 + C + D := by have := sq_mul_le_cubes γ β hγ hβ; linarith
  have hp1 : 0 < α ^ 2 * β := by positivity
  have hp2 : 0 < γ ^ 2 * β := by positivity
  have hprod : (α ^ 2 * β) ^ 2 * (γ ^ 2 * β) ^ 2 ≤ (1 + A + B) ^ 2 * (1 + C + D) ^ 2 := by
    gcongr
  have hδ4 : 0 < (δ ^ 4)⁻¹ := by positivity
  calc ((1 + A + B) ^ 2 * (1 + C + D) ^ 2)⁻¹ ≤ ((α ^ 2 * β) ^ 2 * (γ ^ 2 * β) ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) hprod
    _ = (α ^ 4)⁻¹ * (γ ^ 4)⁻¹ * (β ^ 4)⁻¹ := by
        rw [← mul_inv, ← mul_inv]; congr 1; ring
    _ ≤ (α ^ 4)⁻¹ * (γ ^ 4)⁻¹ * ((β ^ 4)⁻¹ + (δ ^ 4)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith

end GlobalTheory.FlagGram

namespace GlobalTheory

theorem flagGram_density_ineq : ∀ a b c : ℂ, ((1 + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ 2 * (1 + ‖c‖ ^ 2 + ‖a * c - b‖ ^ 2) ^ 2)⁻¹ ≤ (1 + ‖a‖ ^ 2) ^ (-(4 / 3 : ℝ)) * (1 + ‖c‖ ^ 2) ^ (-(4 / 3 : ℝ)) * ((1 + ‖b‖ ^ 2) ^ (-(4 / 3 : ℝ)) + (1 + ‖a * c - b‖ ^ 2) ^ (-(4 / 3 : ℝ))) := by
  intro a b c
  rcases le_total (‖b‖ ^ 2) (‖a * c - b‖ ^ 2) with h | h
  · exact FlagGram.key _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity) h
  · have := FlagGram.key (‖c‖ ^ 2) (‖a * c - b‖ ^ 2) (‖a‖ ^ 2) (‖b‖ ^ 2)
      (by positivity) (by positivity) (by positivity) (by positivity) h
    calc _ = ((1 + ‖c‖ ^ 2 + ‖a * c - b‖ ^ 2) ^ 2 * (1 + ‖a‖ ^ 2 + ‖b‖ ^ 2) ^ 2)⁻¹ := by
          rw [mul_comm]
      _ ≤ _ := this
      _ = _ := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagRowUnipotentMemPeriodUnipotentIntegralGL
section
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

namespace GlobalTheory.DiagVol

theorem rowElt_mem : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (t : n ⊕ Fin c) (y : n ⊕ Fin c → k),
    (∀ s, y s ∈ 𝒪[k]) → (∀ s, ¬ ordL c t < ordL c s → y s = 0) →
    ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c), x.val = 1 + Matrix.of (fun r s => if r = t then y s else 0) := by
  intro k _ _ _ _ n _ _ c t y hy h0
  set E : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k := Matrix.of (fun r s => if r = t then y s else 0) with hE
  have yt : y t = 0 := h0 t (lt_irrefl _)
  have hEE : E * E = 0 := by
    ext r s
    simp [hE, Matrix.mul_apply, yt]
  have h1 : (1 + E) * (1 - E) = 1 := by
    simp only [add_mul, mul_sub, one_mul, mul_one, hEE]; abel
  have h2 : (1 - E) * (1 + E) = 1 := by
    simp only [sub_mul, mul_add, one_mul, mul_one, hEE]; abel
  let M : GL (n ⊕ Fin c) k := ⟨1 + E, 1 - E, h1, h2⟩
  refine ⟨M, Subgroup.mem_inf.2 ⟨?_, ?_⟩, rfl⟩
  · have key : ∀ p, (∀ s, lev p s ≤ lev p t → y s = 0) → M ∈ N k n c p := by
      intro p hp
      rw [Model.mem_N_iff]
      intro r s hrs
      show (1 + E) r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s
      rw [Matrix.add_apply, hE, Matrix.of_apply]
      split_ifs with hr
      · subst hr; rw [hp s hrs, add_zero]
      · rw [add_zero]
    unfold symN
    rcases t with x | i
    · refine Subgroup.mem_sup_left (key _ fun s hs => h0 s ?_)
      rcases s with z | j <;> simp [ordL, lev] at hs ⊢ <;> omega
    · refine Subgroup.mem_sup_right (key _ fun s hs => h0 s ?_)
      rcases s with z | j <;> simp [ordL, lev] at hs ⊢ <;> omega
  · rw [mem_KO_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show (1 + E) i j ∈ 𝒪[k]
      simp only [Matrix.add_apply, hE, Matrix.of_apply, Matrix.one_apply]
      refine add_mem ?_ ?_ <;> split_ifs <;> first | exact one_mem _ | exact zero_mem _ | exact hy _
    · show (1 - E) i j ∈ 𝒪[k]
      simp only [Matrix.sub_apply, hE, Matrix.of_apply, Matrix.one_apply]
      refine sub_mem ?_ ?_ <;> split_ifs <;> first | exact one_mem _ | exact zero_mem _ | exact hy _

end GlobalTheory.DiagVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHermUnitSectionAvoid
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
open scoped Simplicial
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.EZ.Cone

theorem homExt {m a : ℕ} {f g : ⦋m⦌ ⟶ ⦋a⦌}
    (h : ∀ j : Fin (m + 1), (f.toOrderHom j : ℕ) = g.toOrderHom j) : f = g :=
  SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun j => Fin.ext (h j)))

def cv {n a : ℕ} (f : ⦋n⦌ ⟶ ⦋a⦌) : ⦋n + 1⦌ ⟶ ⦋a⦌ :=
  SimplexCategory.mkHom ⟨fun j => if h : (j : ℕ) = 0 then 0 else
      f.toOrderHom ⟨(j : ℕ) - 1, by have := j.2; change _ < n + 1; omega⟩, by
    intro i j hij
    have hij' : (i : ℕ) ≤ j := hij
    dsimp only
    split_ifs with hi hj hj
    · exact le_refl _
    · exact Fin.zero_le _
    · omega
    · exact f.toOrderHom.monotone (show ((⟨(i : ℕ) - 1, _⟩ : Fin _) ≤ ⟨(j : ℕ) - 1, _⟩) from by
        rw [Fin.mk_le_mk]; omega)⟩

theorem cv_apply {n a : ℕ} (f : ⦋n⦌ ⟶ ⦋a⦌) (j : Fin (n + 2)) :
    ((cv f).toOrderHom j : ℕ) = if h : (j : ℕ) = 0 then 0 else
      (f.toOrderHom ⟨(j : ℕ) - 1, by have := j.2; change _ < n + 1; omega⟩ : ℕ) := by
  simp only [cv, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk]
  split_ifs <;> rfl

theorem fc_apply (n m i : ℕ) (j : Fin (m + 1)) :
    ((fc n m i).toOrderHom j : ℕ) = min n (faceFun i j) := rfl

theorem idc_apply (n m : ℕ) (j : Fin (m + 1)) :
    ((idc n m).toOrderHom j : ℕ) = min n j := rfl

theorem face_cone_identity_zero {m a : ℕ} (f : ⦋m⦌ ⟶ ⦋a⦌) : fc (m + 1) m 0 ≫ cv f = f := by
  apply homExt; intro j
  rw [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, cv_apply]
  have h1 : ((fc (m + 1) m 0).toOrderHom j : ℕ) = j + 1 := by
    rw [fc_apply]; unfold faceFun; have := j.2; split_ifs <;> omega
  rw [dite_eq_right (by omega)]
  congr 2; apply Fin.ext; simp only [h1]; omega

theorem fcs_cv {m a : ℕ} (f : ⦋m + 1⦌ ⟶ ⦋a⦌) (k : ℕ) :
    fc (m + 2) (m + 1) (k + 1) ≫ cv f = cv (fc (m + 1) m k ≫ f) := by
  apply homExt; intro j
  rw [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, cv_apply, cv_apply]
  have hj := j.2
  by_cases h0 : (j : ℕ) = 0
  · rw [dite_eq_left h0]
    have : ((fc (m + 2) (m + 1) (k + 1)).toOrderHom j : ℕ) = 0 := by
      rw [fc_apply]; unfold faceFun; split_ifs <;> omega
    rw [dite_eq_left this]
  · have h1 : ((fc (m + 2) (m + 1) (k + 1)).toOrderHom j : ℕ) ≠ 0 := by
      rw [fc_apply]; unfold faceFun; split_ifs <;> omega
    rw [dite_eq_right h1, dite_eq_right h0, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
    congr 2; apply Fin.ext
    simp only [fc_apply]; unfold faceFun; split_ifs <;> omega

theorem face_cone_identity_one {a : ℕ} (f : ⦋0⦌ ⟶ ⦋a⦌) : fc 1 0 1 ≫ cv f = idc a 0 := by
  apply homExt; intro j
  rw [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, cv_apply, idc_apply]
  have hj := j.2
  have : ((fc 1 0 1).toOrderHom j : ℕ) = 0 := by
    rw [fc_apply]; unfold faceFun; split_ifs <;> omega
  rw [dite_eq_left this]; omega

theorem bop_comp {n m p q r s : ℕ} (α : ⦋p⦌ ⟶ ⦋n⦌) (β : ⦋q⦌ ⟶ ⦋m⦌) (α' : ⦋r⦌ ⟶ ⦋p⦌)
    (β' : ⦋s⦌ ⟶ ⦋q⦌) : bop α β ≫ bop α' β' = bop (α' ≫ α) (β' ≫ β) := by
  have h := Free.single_comp_single ℤ (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)
    (show (op ⦋n⦌, op ⦋m⦌) ⟶ (op ⦋p⦌, op ⦋q⦌) from (α.op, β.op))
    (show (op ⦋p⦌, op ⦋q⦌) ⟶ (op ⦋r⦌, op ⦋s⦌) from (α'.op, β'.op)) 1 1
  rw [mul_one] at h
  exact h

def coneHom {a b n : ℕ} (x : (op ⦋a⦌, op ⦋b⦌) ⟶ (op ⦋n⦌, op ⦋n⦌)) :
    (op ⦋a⦌, op ⦋b⦌) ⟶ (op ⦋n + 1⦌, op ⦋n + 1⦌) :=
  ((cv x.1.unop).op, (cv x.2.unop).op)

def cone (a b n : ℕ) : (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1)) :=
  Finsupp.mapDomain.addMonoidHom coneHom

def eps (a b : ℕ) : (bo a b ⟶ bo 0 0) →+ ℤ := Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ)

theorem cone_bop {a b n : ℕ} (α : ⦋n⦌ ⟶ ⦋a⦌) (β : ⦋n⦌ ⟶ ⦋b⦌) :
    cone a b n (bop α β) = bop (cv α) (cv β) := by
  exact Finsupp.mapDomain_single

theorem eps_bop {a b : ℕ} (α : ⦋0⦌ ⟶ ⦋a⦌) (β : ⦋0⦌ ⟶ ⦋b⦌) : eps a b (bop α β) = 1 := by
  exact Finsupp.liftAddHom_apply_single _ _ _

theorem single_eq {a b n p : ℕ} (x : (op ⦋a⦌, op ⦋b⦌) ⟶ (op ⦋n⦌, op ⦋p⦌)) (c : ℤ) :
    (Finsupp.single x c : bo a b ⟶ bo n p) = c • bop x.1.unop x.2.unop := by
  have h := map_zsmul (Finsupp.singleAddHom (M := ℤ) x) c (1 : ℤ)
  rw [smul_eq_mul, mul_one] at h
  exact h

theorem ind {a b n p : ℕ} (P : (bo a b ⟶ bo n p) → Prop) (h0 : P 0) (hadd : ∀ f g, P f → P g → P (f + g))
    (hs : ∀ (α : ⦋n⦌ ⟶ ⦋a⦌) (β : ⦋p⦌ ⟶ ⦋b⦌) (c : ℤ), P (c • bop α β)) (r : bo a b ⟶ bo n p) : P r :=
  Finsupp.induction_linear r h0 hadd (fun x c => by have h := hs x.1.unop x.2.unop c; rw [← single_eq] at h; exact h)

theorem key {a b n : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋a⦌) (β : ⦋n + 1⦌ ⟶ ⦋b⦌) :
    cone a b (n + 1) (bop α β) ≫ dD (n + 2) (n + 1) = bop α β - cone a b n (bop α β ≫ dD (n + 1) n) := by
  rw [cone_bop]
  unfold dD
  rw [ite_eq_left rfl, ite_eq_left rfl]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp, map_sum, map_zsmul, cone_bop]
  rw [Finset.sum_range_succ' _ (n + 2)]
  have h0 : fc (n + 2) (n + 1) 0 ≫ cv α = α := face_cone_identity_zero α
  have h0' : fc (n + 2) (n + 1) 0 ≫ cv β = β := face_cone_identity_zero β
  simp only [h0, h0', fcs_cv, pow_succ, pow_zero, one_smul, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib]
  abel

theorem key0 {a b : ℕ} (α : ⦋0⦌ ⟶ ⦋a⦌) (β : ⦋0⦌ ⟶ ⦋b⦌) :
    cone a b 0 (bop α β) ≫ dD 1 0 = bop α β - bop (idc a 0) (idc b 0) := by
  rw [cone_bop]
  unfold dD
  rw [ite_eq_left rfl]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, bop_comp]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, face_cone_identity_one]
  have h0 : fc 1 0 0 ≫ cv α = α := face_cone_identity_zero α
  have h0' : fc 1 0 0 ≫ cv β = β := face_cone_identity_zero β
  simp only [h0, h0', pow_zero, pow_one, one_smul, neg_smul, zero_add]
  abel

theorem coneContraction : ∃ (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1)))
    (ε : ∀ a b : ℕ, (bo a b ⟶ bo 0 0) →+ ℤ),
    (∀ (a b : ℕ) (α : SimplexCategory.mk 0 ⟶ SimplexCategory.mk a) (β : SimplexCategory.mk 0 ⟶ SimplexCategory.mk b),
      ε a b (bop α β) = 1) ∧
    (∀ (a b : ℕ) (r : bo a b ⟶ bo 0 0), cone a b 0 r ≫ dD 1 0 = r - ε a b r • bop (idc a 0) (idc b 0)) ∧
    ∀ (a b n : ℕ) (r : bo a b ⟶ bo (n + 1) (n + 1)),
      cone a b (n + 1) r ≫ dD (n + 2) (n + 1) = r - cone a b n (r ≫ dD (n + 1) n) := by
  refine ⟨cone, eps, fun a b α β => eps_bop α β, ?_, ?_⟩
  · intro a b r
    refine ind (P := fun r => cone a b 0 r ≫ dD 1 0 = r - eps a b r • bop (idc a 0) (idc b 0)) ?_ ?_ ?_ r
    · rw [map_zero, map_zero, Limits.zero_comp, zero_smul, sub_zero]
    · intro f g hf hg
      simp only [map_add (f := _), Preadditive.add_comp, add_smul, hf, hg]
      abel
    · intro α β c
      rw [map_zsmul, Preadditive.zsmul_comp, key0, map_zsmul, eps_bop, smul_sub, smul_eq_mul, mul_one]
  · intro a b n r
    refine ind (P := fun r => cone a b (n + 1) r ≫ dD (n + 2) (n + 1) = r - cone a b n (r ≫ dD (n + 1) n))
      ?_ ?_ ?_ r
    · rw [map_zero, Limits.zero_comp, Limits.zero_comp, map_zero, sub_zero]
    · intro f g hf hg
      simp only [map_add (f := _), Preadditive.add_comp, hf, hg]
      abel
    · intro α β c
      rw [map_zsmul, Preadditive.zsmul_comp, key, Preadditive.zsmul_comp, map_zsmul, smul_sub]

end GlobalTheory.EZ.Cone
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSections
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.free_hom_sections : ∀ (R : Type) [CommRing R] (P : _root_.GlobalTheory.EtC.PSh)
    (F : _root_.GlobalTheory.EtC.Shv R),
    (∀ a : ∀ U : Scheme.{0}, P.obj (op U) → _root_.GlobalTheory.EtC.Sec F U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) x,
        _root_.GlobalTheory.EtC.Sec.res g (a U x) = a V (P.map g.op x)) →
      ∃ φ : (_root_.GlobalTheory.EtC.free R).obj P ⟶ F, ∀ U x,
        _root_.GlobalTheory.EtC.Sec.map φ (_root_.GlobalTheory.EtC.freeGen R P U x) = a U x) ∧
    (∀ φ ψ : (_root_.GlobalTheory.EtC.free R).obj P ⟶ F,
      (∀ U x, _root_.GlobalTheory.EtC.Sec.map φ (_root_.GlobalTheory.EtC.freeGen R P U x) =
        _root_.GlobalTheory.EtC.Sec.map ψ (_root_.GlobalTheory.EtC.freeGen R P U x)) → φ = ψ) ∧
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) x,
      _root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.freeGen R P U x) =
        _root_.GlobalTheory.EtC.freeGen R P V (P.map g.op x)) ∧
    ∀ (Q : _root_.GlobalTheory.EtC.PSh) (f : P ⟶ Q) U x,
      _root_.GlobalTheory.EtC.Sec.map ((_root_.GlobalTheory.EtC.free R).map f)
          (_root_.GlobalTheory.EtC.freeGen R P U x) =
        _root_.GlobalTheory.EtC.freeGen R Q U (f.app (op U) x) := by
  intro R _ P F
  exact ⟨fun a ha => _root_.GlobalTheory.EtC.CupSpec.free_exists P F a ha,
    fun φ ψ h => _root_.GlobalTheory.EtC.CupSpec.free_ext φ ψ h,
    fun V U g x => _root_.GlobalTheory.EtC.CupSpec.freeGen_res P g x,
    fun Q f U x => _root_.GlobalTheory.EtC.CupSpec.freeGen_map f U x⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

def HInv (q : ℕ) [NeZero q] (A : Type) [CommRing A] : Prop :=
  ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i)

end GlobalTheory.EtC
end

