module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0331
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0332

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSecStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n k : ℤ),
      m + 1 = n → n + 1 = k →
        (∀ z : Sec (I.X n) X, Sec.map (I.d n k) z = 0 →
          ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n,
            (∀ (U : Scheme.{0}) (x : U ⟶ X), ev (R := R) α.1 0 n (by simp) U x = Sec.res x z) ∧
              ∀ (p : ℕ) s h U x, ev (R := R) α.1 (p + 1) s h U x = 0) ∧
        ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n,
          Sec.map (I.d n k) (ev (R := R) α.1 0 n (by simp) X (𝟙 X)) = 0 ∧
            (CohomologyClass.mk α = 0 ↔
              ∃ y : Sec (I.X m) X, Sec.map (I.d m n) y = ev (R := R) α.1 0 n (by simp) X (𝟙 X)) := by
  intro R _ X I m n k hmn hnk
  have ev_def {q : ℤ} (α : Cochain ((chains R).obj (sch.obj X)) I q)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + q = s) (U : Scheme.{0}) (x : Sx (sch.obj X) p U) :
      ev (R := R) α p s h U x =
        Sec.map ((chainsXIso R (sch.obj X) p).inv ≫ α.v _ _ h) (freeGen R _ U x) := rfl
  have ev_ext {q : ℤ} (α β : Cochain ((chains R).obj (sch.obj X)) I q)
      (h : ∀ p s hs U x, ev (R := R) α p s hs U x = ev (R := R) β p s hs U x) : α = β := by
    ext i s hs : 1
    by_cases hi : i ≤ 0
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R (sch.obj X) p).inv]
      exact CupSpec.free_ext _ _ (fun U x => h p s hs U x)
    · exact (CupSpec.isZero_chains (sch.obj X) i (by omega)).eq_of_src _ _
  have ev_exists {q : ℤ}
      (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + q = s → ∀ U : Scheme.{0},
        Sx (sch.obj X) p U → Sec (I.X s) U)
      (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx (sch.obj X) p U),
        Sec.res g (a p s h U x) = a p s h V (x.res g)) :
      ∃ α : Cochain ((chains R).obj (sch.obj X)) I q,
        ∀ p s h U x, ev (R := R) α p s h U x = a p s h U x := by
    have key : ∀ (i j : ℤ) (hij : i + q = j),
        ∃ φ : ((chains R).obj (sch.obj X)).X i ⟶ I.X j,
          ∀ (p : ℕ) (hp : i = -(p : ℤ)) U x,
            Sec.map ((chainsXIso R (sch.obj X) p).inv ≫
              eqToHom (congrArg ((chains R).obj (sch.obj X)).X hp.symm) ≫ φ) (freeGen R _ U x) =
              a p j (hp ▸ hij) U x := by
      intro i j hij
      by_cases hi : i ≤ 0
      · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
        obtain ⟨φ, hφ⟩ := CupSpec.free_exists (R := R) _ _ (a p j hij) (ha p j hij)
        refine ⟨(chainsXIso R (sch.obj X) p).hom ≫ φ, fun p' hp U x => ?_⟩
        obtain rfl : p = p' := by omega
        rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
        exact hφ U x
      · exact ⟨0, fun p hp => by omega⟩
    choose φ hφ using key
    refine ⟨Cochain.mk φ, fun p s h U x => ?_⟩
    have he := hφ _ _ h p rfl U x
    rw [eqToHom_refl, Category.id_comp] at he
    exact he
  have ev_res {q : ℤ} (α : Cochain ((chains R).obj (sch.obj X)) I q)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + q = s) {V U : Scheme.{0}} (g : V ⟶ U)
      (x : Sx (sch.obj X) p U) :
      Sec.res g (ev (R := R) α p s h U x) = ev (R := R) α p s h V (x.res g) := by
    rw [ev_def, CupSpec.map_res, CupSpec.freeGen_res]
    rfl
  have ev_zero {q : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + q = s)
      (U : Scheme.{0}) (x : Sx (sch.obj X) p U) :
      ev (R := R) (0 : Cochain ((chains R).obj (sch.obj X)) I q) p s h U x = 0 := by
    rw [ev_def, Cochain.zero_v, comp_zero]
    exact (CupSpec.mapHom _ _ _).map_zero
  have ev_δ_zero {a b : ℤ} (hab : a + 1 = b)
      (α : Cochain ((chains R).obj (sch.obj X)) I a) (U : Scheme.{0}) (s t : ℤ)
      (hs : -((0 : ℕ) : ℤ) + a = s) (ht : -((0 : ℕ) : ℤ) + b = t) (x : Sx (sch.obj X) 0 U) :
      ev (R := R) (δ a b α) 0 t ht U x = Sec.map (I.d s t) (ev (R := R) α 0 s hs U x) := by
    rw [ev_def, δ_v a b hab α _ t ht s 1 (by omega) (by simp),
      (CupSpec.isZero_chains (sch.obj X) 1 one_pos).eq_of_tgt (((chains R).obj (sch.obj X)).d _ 1) 0,
      zero_comp, smul_zero, add_zero]
    rfl
  have ev_δ_sch {a b : ℤ} (hab : a + 1 = b)
      (α : Cochain ((chains R).obj (sch.obj X)) I a) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
      (hs : -((p + 1 : ℕ) : ℤ) + a = s) (ht : -((p + 1 : ℕ) : ℤ) + b = t)
      (x : Sx (sch.obj X) (p + 1) U) :
      ev (R := R) (δ a b α) (p + 1) t ht U x = Sec.map (I.d s t) (ev (R := R) α (p + 1) s hs U x) +
        (if Even p then 0 else b.negOnePow • ev (R := R) α p t (by omega) U x) := by
    have hsum : ev (R := R) (δ a b α) (p + 1) t ht U x =
        Sec.map (I.d s t) (ev (R := R) α (p + 1) s hs U x) +
          b.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
            ev (R := R) α p t (by omega) U (x.face i) := by
      rw [ev_def, δ_v a b hab α _ t ht s (-(p : ℤ)) (by omega) (by omega),
        Preadditive.comp_add, Units.smul_def, Preadditive.comp_zsmul,
        ← Category.assoc _ (((chains R).obj (sch.obj X)).d _ _), CupSpec.chains_d, Category.assoc,
        Preadditive.sum_comp]
      refine (map_add (CupSpec.mapHom _ _ (freeGen R _ U x)) _ _).trans ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_zsmul, map_sum, Units.smul_def]
      refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
      rw [Preadditive.zsmul_comp, map_zsmul]
      congr 1
      change Sec.map ((chainsXIso R (sch.obj X) p).inv ≫ α.v _ _ _)
        (Sec.map ((free R).map _) (freeGen R _ U x)) = _
      rw [CupSpec.freeGen_map]
      rfl
    rw [hsum]
    simp only [SchCls.face_sch]
    rw [← Finset.sum_smul, SchCls.sum_neg_one_pow]
    split_ifs <;> simp
  refine ⟨fun z hz => ?_, fun α => ?_⟩
  · obtain ⟨a, ha⟩ := ev_exists (q := n)
      (fun p s h U x => if hp : p = 0 then
        Sec.map (I.XIsoOfEq (show n = s by omega)).hom (Sec.res (x : U ⟶ X) z) else 0)
      (by
        intro p s h V U g x
        by_cases hp : p = 0
        · subst hp
          simp only [dite_eq_left]
          erw [CupSpec.map_res, SchCls.res_comp]
          rfl
        · simp only [dite_eq_right hp]
          exact map_zero _)
    have hc : δ n k a = 0 := by
      refine ev_ext _ _ fun p t ht U x => ?_
      erw [ev_zero]
      cases p with
      | zero =>
        have hkt : k = t := by omega
        subst hkt
        erw [ev_δ_zero hnk a U n k (by simp) ht x, ha]
        simp only [dite_eq_left, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, SchCls.map_id']
        erw [← CupSpec.map_res, hz]
        exact map_zero _
      | succ p =>
        erw [ev_δ_sch hnk a U p (-((p + 1 : ℕ) : ℤ) + n) t (by omega) ht x, ha, ha]
        simp only [Nat.add_one_ne_zero, dite_eq_right, not_false_eq_true, map_zero, zero_add]
        split_ifs with he hp0
        · rfl
        · exact absurd (hp0 ▸ (⟨0, rfl⟩ : Even 0)) he
        · exact smul_zero _
    refine ⟨Cocycle.mk a k hnk hc, fun U x => ?_, fun p s h U x => ?_⟩
    · change ev (R := R) a 0 n _ U x = _
      erw [ha]
      simp only [dite_eq_left, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, SchCls.map_id']
    · change ev (R := R) a (p + 1) s h U x = 0
      erw [ha]
      simp
  · have hδ := Cocycle.δ_eq_zero α k
    refine ⟨?_, ?_⟩
    · have h0 := ev_δ_zero hnk α.1 X n k (by simp) (by simp) (𝟙 X)
      erw [hδ, ev_zero] at h0
      exact h0.symm
    erw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff α m hmn]
    constructor
    · rintro ⟨β, hβ⟩
      refine ⟨ev (R := R) β 0 m (by simp) X (𝟙 X), ?_⟩
      erw [← hβ, ev_δ_zero hmn β X m n (by simp) (by simp)]
    · rintro ⟨y, hy⟩
      obtain ⟨b, hb⟩ := ev_exists (q := m)
        (fun p s h U x => if hp : p = 0 then
          Sec.map (I.XIsoOfEq (show m = s by omega)).hom (Sec.res (x : U ⟶ X) y)
          else if Even p then 0 else (-k.negOnePow) • ev (R := R) α.1 (p + 1) s (by omega) U x)
        (by
          intro p s h V U g x
          by_cases hp : p = 0
          · subst hp
            simp only [dite_eq_left]
            erw [CupSpec.map_res, SchCls.res_comp]
            rfl
          · simp only [dite_eq_right hp]
            split_ifs
            · exact map_zero _
            · erw [SchCls.res_units_smul, ev_res]
              rfl)
      refine ⟨b, ev_ext _ _ fun p t ht U x => ?_⟩
      cases p with
      | zero =>
        have hnt : n = t := by omega
        subst hnt
        erw [ev_δ_zero hmn b U m n (by simp) ht x, hb]
        simp only [dite_eq_left, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, SchCls.map_id']
        erw [← CupSpec.map_res, hy, ev_res]
        congr 1
      | succ p =>
        erw [ev_δ_sch hmn b U p (-((p + 1 : ℕ) : ℤ) + m) t (by omega) ht x, hb, hb]
        have hc := ev_δ_sch hnk α.1 U (p + 1) (-((p + 1 : ℕ) : ℤ) + m) t (by omega) (by omega) x
        erw [hδ, ev_zero] at hc
        rcases Nat.even_or_odd p with he | ho
        · have hne : ¬ Even (p + 1) := Nat.not_even_iff_odd.mpr he.add_one
          simp only [Nat.add_one_ne_zero, dite_eq_right, not_false_eq_true, hne, ite_false, ite_eq_left he,
            add_zero] at hc ⊢
          erw [SchCls.map_units_smul, eq_neg_of_add_eq_zero_left hc.symm, smul_neg, smul_smul]
          simp [Int.units_mul_self]
        · have hne : ¬ Even p := Nat.not_even_iff_odd.mpr ho
          have hp0 : p ≠ 0 := fun h => hne (h ▸ (⟨0, rfl⟩ : Even 0))
          have hev : Even (p + 1) := ho.add_one
          simp only [Nat.add_one_ne_zero, dite_eq_right, not_false_eq_true, hev, ite_true, hne, ite_false,
            dite_eq_right hp0, map_zero, zero_add]
          have hkn : k.negOnePow = -n.negOnePow := by rw [← hnk, Int.negOnePow_succ]
          erw [hkn, neg_neg, smul_smul, Int.units_mul_self, one_smul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTensorRightOperator
section
open GlobalTheory.SliceSchwartz
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SliceOp
open GlobalTheory.SliceSchwartz

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']

theorem contDiff_qOp_nat (n : ℕ) : ∀ (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ), ContDiff ℝ n (qOp P f) := by
  induction n with
  | zero => intro P f; exact contDiff_zero.2 (GlobalTheory.T.partial_operator_fderiv_formula V κ κ' κ₁' P f).1.continuous
  | succ n ih =>
    intro P f
    obtain ⟨hd, hf⟩ := GlobalTheory.T.partial_operator_fderiv_formula V κ κ' κ₁' P f
    have e : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [e, contDiff_succ_iff_fderiv_apply]
    refine ⟨hd, by simp, fun v => ?_⟩
    have : (fun s => fderiv ℝ (qOp P f) s v) = fun s =>
        qOp P (pd (padL (κ' := κ') (v ∘ Sum.inl)) f) s + qOp ((pd (v ∘ Sum.inr)).comp P) f s :=
      funext fun s => hf s v
    rw [this]
    exact (ih _ _).add (ih _ _)

theorem contDiff_qOp (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) : ContDiff ℝ ∞ (qOp P f) :=
  contDiff_infty.2 fun n => contDiff_qOp_nat n P f

theorem decay_qOp (n : ℕ) : ∀ (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (k : ℕ),
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (z : κ ⊕ κ₁' → V),
      ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (qOp P f) z‖ ≤ C * s.sup (schwartzSeminormFamily ℂ (κ ⊕ κ' → V) ℂ) f := by
  induction n with
  | zero =>
    intro P k
    obtain ⟨s, C, hC, h⟩ := _root_.GlobalTheory.SliceOpDecay.decay V κ κ' κ₁' P k
    exact ⟨s, C, hC, fun f z => by rw [norm_iteratedFDeriv_zero]; exact h f z⟩
  | succ n ih =>
    intro P k
    obtain ⟨CE, hCE, hE⟩ := _root_.GlobalTheory.norm_iteratedFDeriv_succ_le_sum_partial (κ ⊕ κ₁' → V)
    set b := Module.finBasis ℝ (κ ⊕ κ₁' → V)
    obtain ⟨s1, C1, hC1, h1⟩ := ih P k
    choose s1' C1' hC1' h1' using fun i => clm_sup_bound (pd (padL (κ' := κ') (b i ∘ Sum.inl))) s1
    choose s2 C2 hC2 h2 using fun i => ih ((pd (b i ∘ Sum.inr)).comp P) k
    refine ⟨Finset.univ.sup (fun i => s1' i ∪ s2 i), CE * ∑ i, (C1 * C1' i + C2 i),
      mul_nonneg hCE (Finset.sum_nonneg fun i _ => add_nonneg (mul_nonneg hC1 (hC1' i)) (hC2 i)), fun f z => ?_⟩
    set p := schwartzSeminormFamily ℂ (κ ⊕ κ' → V) ℂ
    set S := (Finset.univ.sup (fun i => s1' i ∪ s2 i)).sup p f
    have hmono : ∀ i (t : Finset (ℕ × ℕ)), t ⊆ s1' i ∪ s2 i → t.sup p f ≤ S := by
      intro i t ht
      exact Seminorm.le_def.1 (Finset.sup_mono (ht.trans
        (Finset.le_sup (f := fun i => s1' i ∪ s2 i) (Finset.mem_univ i)))) f
    have key : ∀ i, ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ (qOp P f) w (b i)) z‖
        ≤ (C1 * C1' i + C2 i) * S := by
      intro i
      have hfun : (fun w => fderiv ℝ (qOp P f) w (b i)) =
          qOp P (pd (padL (κ' := κ') (b i ∘ Sum.inl)) f) + qOp ((pd (b i ∘ Sum.inr)).comp P) f :=
        funext fun w => (GlobalTheory.T.partial_operator_fderiv_formula V κ κ' κ₁' P f).2 w (b i)
      rw [hfun, iteratedFDeriv_add_apply (contDiff_qOp_nat n _ _).contDiffAt (contDiff_qOp_nat n _ _).contDiffAt]
      have e1 := h1 (pd (padL (κ' := κ') (b i ∘ Sum.inl)) f) z
      have e1' := h1' i f
      have e2 := h2 i f z
      have m1 := hmono i (s1' i) Finset.subset_union_left
      have m2 := hmono i (s2 i) Finset.subset_union_right
      have hz : 0 ≤ ‖z‖ ^ k := by positivity
      calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (qOp P (pd (padL (κ' := κ') (b i ∘ Sum.inl)) f)) z +
              iteratedFDeriv ℝ n (qOp ((pd (b i ∘ Sum.inr)).comp P) f) z‖
          ≤ ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (qOp P (pd (padL (κ' := κ') (b i ∘ Sum.inl)) f)) z‖ +
              ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (qOp ((pd (b i ∘ Sum.inr)).comp P) f) z‖ := by
            rw [← mul_add]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hz
        _ ≤ C1 * (C1' i * S) + C2 i * S := by
            refine add_le_add (e1.trans (mul_le_mul_of_nonneg_left (e1'.trans
              (mul_le_mul_of_nonneg_left m1 (hC1' i))) hC1)) (e2.trans (mul_le_mul_of_nonneg_left m2 (hC2 i)))
        _ = (C1 * C1' i + C2 i) * S := by ring
    have hz : 0 ≤ ‖z‖ ^ k := by positivity
    calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) (qOp P f) z‖
        ≤ ‖z‖ ^ k * (CE * ∑ i, ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ (qOp P f) w (b i)) z‖) :=
          mul_le_mul_of_nonneg_left (hE _ (contDiff_qOp P f) n z) hz
      _ = CE * ∑ i, ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ (qOp P f) w (b i)) z‖ := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; congr 1; funext i; ring
      _ ≤ CE * ∑ i, (C1 * C1' i + C2 i) * S :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => key i) hCE
      _ = (CE * ∑ i, (C1 * C1' i + C2 i)) * S := by rw [mul_assoc, Finset.sum_mul]

end GlobalTheory.SliceOp

open GlobalTheory.SliceOp in
theorem GlobalTheory.SliceOp.exists_tensor_clm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type)
    [Fintype κ] [Fintype κ'] [Fintype κ₁'] (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ),
    ∃ Q : SchwartzMap (κ ⊕ κ' → V) ℂ →L[ℂ] SchwartzMap (κ ⊕ κ₁' → V) ℂ,
      ∀ (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (s : κ ⊕ κ₁' → V), Q f s = P (sliceR f (s ∘ Sum.inl)) (s ∘ Sum.inr) := by
  intro V _ _ _ κ κ' κ₁' _ _ _ P
  refine ⟨SchwartzMap.mkCLM (σ := RingHom.id ℂ) (fun f => qOp P f) ?_ ?_ ?_ ?_, fun f s => rfl⟩
  · intro f g s
    simp only [qOp, ← sliceRL_apply, map_add (f := _), SchwartzMap.add_apply]
  · intro a f s
    simp only [qOp, ← sliceRL_apply, map_smul, SchwartzMap.smul_apply, RingHom.id_apply]
  · intro f; exact contDiff_qOp P f
  · rintro ⟨k, n⟩; exact decay_qOp n P k
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafSectionEqZeroAtStageOfFilteredColimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FilteredSections

variable {R : Type} [CommRing R]

lemma etale_of_isPushout {A B C P : CommRingCat.{0}} {g : A ⟶ B} {f : A ⟶ C} {inl : B ⟶ P}
    {inr : C ⟶ P} (sq : IsPushout g f inl inr) (hg : g.hom.Etale) : inr.hom.Etale := by
  have : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty @RingHom.Etale) sq.flip hg

lemma cover_of_isPushout {ι : Type} {A C : CommRingCat.{0}} {B P : ι → CommRingCat.{0}}
    (g : ∀ i, A ⟶ B i) (f : A ⟶ C) (inl : ∀ i, B i ⟶ P i) (inr : ∀ i, C ⟶ P i)
    (sq : ∀ i, IsPushout (g i) f (inl i) (inr i))
    (hcov : ∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) :
    ∀ p : Spec C, ∃ i v, Spec.map (inr i) v = p := by
  intro p
  obtain ⟨i, v, hv⟩ := hcov (Spec.map f p)
  obtain ⟨z, hz⟩ := GlobalTheory.EtaleCoverDescent.exists_point_of_isPushout (sq i).flip p v hv.symm
  exact ⟨i, z, hz⟩

lemma eq_zero_of_cover (F : Shv R) {ι : Type} {A : CommRingCat.{0}} {B : ι → CommRingCat.{0}}
    (g : ∀ i, A ⟶ B i) (hg : ∀ i, (g i).hom.Etale)
    (hcov : ∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) (y : (onRings F).obj A)
    (hy : ∀ i, ((onRings F).map (g i)).hom y = 0) : y = 0 :=
  (GlobalTheory.EtC.sec_sep_glue_of_points R F (Spec A) ι (fun i => Spec (B i)) (fun i => Spec.map (g i))
    (fun i => (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (hg i)) hcov).1 y hy

lemma map_eta {M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)} {F : Shv R}
    (η : M ⟶ onRings F) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : M.obj A) :
    ((onRings F).map f).hom ((η.app A).hom x) = (η.app B).hom ((M.map f).hom x) := by
  change (η.app A ≫ (onRings F).map f).hom x = (M.map f ≫ η.app B).hom x
  rw [η.naturality]

lemma stage_of_pieces (F : Shv R) {J : Type} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (j : J) (y : (onRings F).obj (D.obj j)) {ι : Type} [Finite ι]
    (B : ι → CommRingCat.{0}) (g : ∀ i, D.obj j ⟶ B i) (hg : ∀ i, (g i).hom.Etale)
    (hcov : ∀ p : Spec (D.obj j), ∃ i v, Spec.map (g i) v = p)
    (D' : ι → (Under j ⥤ CommRingCat.{0})) (u : ∀ i, Under.forget j ⋙ D ⟶ D' i)
    (v : ∀ i, (Functor.const _).obj (B i) ⟶ D' i)
    (sq : ∀ i (k : Under j), IsPushout (g i) (D.map k.hom) ((v i).app k) ((u i).app k))
    (hk : ∀ i, ∃ k : Under j,
      ((onRings F).map ((v i).app k)).hom (((onRings F).map (g i)).hom y) = 0) :
    ∃ (k : J) (f : j ⟶ k), ((onRings F).map (D.map f)).hom y = 0 := by
  classical
  choose k hk using hk
  letI := Fintype.ofFinite ι
  obtain ⟨K, hK⟩ := IsFiltered.sup_objs_exists (Finset.univ.image k)
  have e : ∀ i, k i ⟶ K := fun i => (hK (Finset.mem_image_of_mem _ (Finset.mem_univ i))).some
  refine ⟨K.right, K.hom, ?_⟩
  apply eq_zero_of_cover F (fun i => (u i).app K) (fun i => etale_of_isPushout (sq i K) (hg i))
    (cover_of_isPushout g (D.map K.hom) (fun i => (v i).app K) (fun i => (u i).app K)
      (fun i => sq i K) hcov)
  intro i
  have h1 : (v i).app (k i) ≫ (D' i).map (e i) = (v i).app K := by
    simpa using ((v i).naturality (e i)).symm
  have h2 : D.map K.hom ≫ (u i).app K = g i ≫ (v i).app K := (sq i K).w.symm
  have h3 : ((onRings F).map ((u i).app K)).hom (((onRings F).map (D.map K.hom)).hom y) =
      ((onRings F).map ((D' i).map (e i))).hom
        (((onRings F).map ((v i).app (k i))).hom (((onRings F).map (g i)).hom y)) := by
    have := congrArg (fun φ => ((onRings F).map φ).hom y) h2
    rw [← h1] at this
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at this
    exact this
  rw [h3, hk i, map_zero]

lemma stage_of_eta (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R)
    (η : M ⟶ onRings F) (hM : PreservesFilteredColimitsOfSize.{0, 0} M)
    (hker : ∀ (A : CommRingCat.{0}) (m : M.obj A), (η.app A).hom m = 0 → ∃ (ι : Type) (_ : Finite ι)
      (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i), (∀ i, (g i).hom.Etale) ∧
      (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (M.map (g i)).hom m = 0)
    (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) (j : J) (m : M.obj (D.obj j))
    (hm : ((onRings F).map (c.ι.app j)).hom ((η.app _).hom m) = 0) :
    ∃ (k : J) (f : j ⟶ k), ((onRings F).map (D.map f)).hom ((η.app _).hom m) = 0 := by
  have hMel := (GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_modules_iff_elements _ M).2.1 hM
  rw [map_eta] at hm
  obtain ⟨ι, _, B, g, hg, hcov, hz⟩ := hker _ _ hm
  obtain ⟨j', f0, B', g', h, hsq, hcov'⟩ :=
    GlobalTheory.EtaleCoverDescent.exists_etale_cover_model_of_isColimit J D c hc ι B g hg hcov j
  choose D' ιB u v hcol hpush using fun i =>
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J D c hc j' (B' i) (B i) (g' i) (h i) (g i)
      (hsq i).2
  have hk : ∀ i, ∃ k : Under j', ((onRings F).map ((v i).app k)).hom
      (((onRings F).map (g' i)).hom ((η.app _).hom ((M.map (D.map f0)).hom m))) = 0 := by
    intro i
    let k0 : Under j' := Under.mk (𝟙 j')
    have e1 : D.map f0 ≫ g' i ≫ (v i).app k0 ≫ (ιB i).app k0 = c.ι.app j ≫ g i := by
      rw [(hpush i k0).2.1, (hsq i).2.w, ← Category.assoc, c.w]
    have hdie : (M.map ((ιB i).app k0)).hom ((M.map ((v i).app k0)).hom
        ((M.map (g' i)).hom ((M.map (D.map f0)).hom m))) = 0 := by
      have := congrArg (fun φ => (M.map φ).hom m) e1
      simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at this
      rw [this]
      exact hz i
    obtain ⟨k, f, hf⟩ := (hMel (Under j') (D' i) _ (hcol i).some).2 k0 _ hdie
    refine ⟨k, ?_⟩
    have e2 : (v i).app k0 ≫ (D' i).map f = (v i).app k := by
      simpa using ((v i).naturality f).symm
    rw [map_eta]
    erw [map_eta]
    rw [← e2, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hf,
      map_zero]
  obtain ⟨k, f, hf⟩ := stage_of_pieces F D j' ((η.app _).hom ((M.map (D.map f0)).hom m)) B' g'
    (fun i => (hsq i).1) hcov' D' u v (fun i k => (hpush i k).1) hk
  refine ⟨k, f0 ≫ f, ?_⟩
  rw [map_eta] at hf ⊢
  rw [Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact hf

theorem eq_zero_at_stage_of_map_colimit_eq_zero : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R) (η : M ⟶ onRings F), PreservesFilteredColimitsOfSize.{0, 0} M → (∀ (A : CommRingCat.{0}) (x : (onRings F).obj A), ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i) (m : ∀ i, M.obj (B i)), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (η.app (B i)).hom (m i) = ((onRings F).map (g i)).hom x) → (∀ (A : CommRingCat.{0}) (m : M.obj A), (η.app A).hom m = 0 → ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (M.map (g i)).hom m = 0) → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (j : J) (y : (onRings F).obj (D.obj j)), ((onRings F).map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), ((onRings F).map (D.map f)).hom y = 0 := by
  intro R _ M F η hM hloc hker J _ _ D c hc j y hy
  obtain ⟨ι, _, B, g, m, hg, hcov, hm⟩ := hloc _ y
  have hP : ∀ i, IsPushout (g i) (c.ι.app j) (pushout.inl (g i) (c.ι.app j))
      (pushout.inr (g i) (c.ι.app j)) := fun i => IsPushout.of_hasPushout _ _
  choose D' ιB u v hcol hpush using fun i =>
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J D c hc j (B i)
      (pushout (g i) (c.ι.app j)) (g i) (pushout.inl (g i) (c.ι.app j))
      (pushout.inr (g i) (c.ι.app j)) (hP i)
  have hk : ∀ i, ∃ k : Under j,
      ((onRings F).map ((v i).app k)).hom (((onRings F).map (g i)).hom y) = 0 := by
    intro i
    let k0 : Under j := Under.mk (𝟙 j)
    have h0 : ((onRings F).map ((ιB i).app k0)).hom
        ((η.app _).hom ((M.map ((v i).app k0)).hom (m i))) = 0 := by
      calc ((onRings F).map ((ιB i).app k0)).hom ((η.app _).hom ((M.map ((v i).app k0)).hom (m i)))
          = (η.app _).hom ((M.map ((v i).app k0 ≫ (ιB i).app k0)).hom (m i)) := by
            rw [map_eta, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
        _ = ((onRings F).map (pushout.inl (g i) (c.ι.app j))).hom ((η.app _).hom (m i)) := by
            rw [(hpush i k0).2.1, map_eta]
            rfl
        _ = ((onRings F).map (g i ≫ pushout.inl (g i) (c.ι.app j))).hom y := by
            rw [hm i, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
        _ = 0 := by
            rw [pushout.condition, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hy,
              map_zero]
    obtain ⟨k, f, hf⟩ := stage_of_eta M F η hM hker (Under j) (D' i) _ (hcol i).some k0 _ h0
    refine ⟨k, ?_⟩
    have e2 : (v i).app k0 ≫ (D' i).map f = (v i).app k := by
      simpa using ((v i).naturality f).symm
    rw [← hm i]
    erw [map_eta]
    rw [← e2, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
      ← map_eta]
    exact hf
  exact stage_of_pieces F D j y B g hg hcov D' u v (fun i k => (hpush i k).1) hk

end GlobalTheory.EtC.FilteredSections
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardSimplexFacePairsAcyclicPositiveDegreeStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardSimplexFacePairs_acyclic_positive_degree : ∀ N k (c : Pr N →₀ ℤ), Pr.Deg (k + 1) c → Pr.d N c = 0 → ∃ e, Pr.Deg (k + 2) e ∧ Pr.d N e = c := by
  first | (exact @GlobalTheory.PrAcyc.pr_acyclic) | (exact GlobalTheory.PrAcyc.pr_acyclic) | (intros; apply GlobalTheory.PrAcyc.pr_acyclic  <;> assumption)
end

