module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSec
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SchCls

theorem sum_neg_one_pow (p : ℕ) : ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) = if Even p then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i)]
  induction p with
  | zero => simp [Finset.sum_range_succ]
  | succ q ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd q with h | h
    · have h2 : Even (q + 1 + 1) := by rw [add_assoc]; exact h.add even_two
      simp [h, Nat.even_add_one, h2.neg_one_pow]
    · have h2 : Odd (q + 1 + 1) := by rw [add_assoc]; exact h.add_even even_two
      have h3 : Even (q + 1) := h.add_one
      simp [h3, h2.neg_one_pow, Nat.not_even_iff_odd.mpr h]

variable {R : Type} [CommRing R]

theorem face_sch {X U : Scheme.{0}} {p : ℕ} (x : Sx (sch.obj X) (p + 1) U) (i : Fin (p + 2)) : x.face i = x := rfl

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (z : Sec F U) :
    Sec.res g (Sec.res f z) = Sec.res (g ≫ f) z := by
  simp [Sec.res]

theorem map_id' {F : Shv R} {U : Scheme.{0}} (y : Sec F U) : Sec.map (𝟙 F) y = y := rfl

theorem map_units_smul {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (u : ℤˣ) (y : Sec F U) :
    Sec.map φ (u • y) = u • Sec.map φ y := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem res_units_smul {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (u : ℤˣ) (y : Sec F U) :
    Sec.res g (u • y) = u • Sec.res g y := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem ev_δ_sch {X : Scheme.{0}} {I : Cx R} {n k : ℤ} (hk : n + 1 = k)
    (α : Cochain ((chains R).obj (sch.obj X)) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
    (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + k = t) (x : Sx (sch.obj X) (p + 1) U) :
    ev (δ n k α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
      (if Even p then 0 else k.negOnePow • ev α p t (by omega) U x) := by
  have hsum :
      ev (δ n k α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
        k.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U x := by
    change Sec.map ((chainsXIso R (sch.obj X) (p + 1)).inv ≫ (δ n k α).v _ _ ht)
      (freeGen R _ U x) = _
    rw [δ_v n k hk α _ t ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add,
      Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj (sch.obj X)).d _ _),
      CupSpec.chains_d, Category.assoc, Preadditive.sum_comp]
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
  rw [← Finset.sum_smul, sum_neg_one_pow]
  split_ifs <;> simp

end GlobalTheory.EtC.SchCls

namespace GlobalTheory.EtC


open GlobalTheory.EtC.SchCls in
theorem sch_cls_cocycle_sec : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n k : ℤ),
    m + 1 = n → n + 1 = k →
      (∀ z : Sec (I.X n) X, Sec.map (I.d n k) z = 0 →
        ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n,
          (∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 n (by simp) U x = Sec.res x z) ∧
            ∀ (p : ℕ) s h U x, ev α.1 (p + 1) s h U x = 0) ∧
      ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n,
        Sec.map (I.d n k) (ev α.1 0 n (by simp) X (𝟙 X)) = 0 ∧
          (CohomologyClass.mk α = 0 ↔
            ∃ y : Sec (I.X m) X, Sec.map (I.d m n) y = ev α.1 0 n (by simp) X (𝟙 X)) := by
  intro R _ X I m n k hmn hnk
  have ev_exists {j : ℤ}
      (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + j = s →
        ∀ U : Scheme.{0}, Sx (sch.obj X) p U → Sec (I.X s) U)
      (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx (sch.obj X) p U),
        Sec.res g (a p s h U x) = a p s h V (x.res g)) :
      ∃ α : Cochain ((chains R).obj (sch.obj X)) I j,
        ∀ p s h U x, ev α p s h U x = a p s h U x := by
    have key : ∀ (i s : ℤ) (h : i + j = s),
        ∃ φ : ((chains R).obj (sch.obj X)).X i ⟶ I.X s,
          ∀ (p : ℕ) (hp : i = -(p : ℤ)) U x,
            Sec.map ((chainsXIso R (sch.obj X) p).inv ≫
              eqToHom (congrArg ((chains R).obj (sch.obj X)).X hp.symm) ≫ φ) (freeGen R _ U x) =
                a p s (hp ▸ h) U x := by
      intro i s h
      by_cases hi : i ≤ 0
      · obtain ⟨q, rfl⟩ : ∃ q : ℕ, i = -(q : ℤ) := ⟨(-i).toNat, by omega⟩
        obtain ⟨φ, hφ⟩ := CupSpec.free_exists (R := R) _ _ (a q s h) (ha q s h)
        refine ⟨(chainsXIso R (sch.obj X) q).hom ≫ φ, fun p hp U x => ?_⟩
        obtain rfl : q = p := by omega
        rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
        exact hφ U x
      · exact ⟨0, fun p hp => by omega⟩
    choose φ hφ using key
    refine ⟨Cochain.mk φ, fun p s h U x => ?_⟩
    have heval := hφ _ _ h p rfl U x
    rw [eqToHom_refl, Category.id_comp] at heval
    exact heval
  have ev_δ_zero {i j : ℤ} (hij : i + 1 = j)
      (a : Cochain ((chains R).obj (sch.obj X)) I i) (U : Scheme.{0}) (s t : ℤ)
      (hs : -((0 : ℕ) : ℤ) + i = s) (ht : -((0 : ℕ) : ℤ) + j = t) (x : Sx (sch.obj X) 0 U) :
      ev (δ i j a) 0 t ht U x = Sec.map (I.d s t) (ev a 0 s hs U x) := by
    change Sec.map ((chainsXIso R (sch.obj X) 0).inv ≫ (δ i j a).v _ _ ht) (freeGen R _ U x) = _
    rw [δ_v i j hij a _ t ht s 1 (by omega) (by simp),
      (CupSpec.isZero_chains (R := R) (sch.obj X) 1 one_pos).eq_of_tgt
        (((chains R).obj (sch.obj X)).d _ 1) 0, zero_comp, smul_zero, add_zero]
    rfl
  have ev_zero {j : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + j = s)
      (U : Scheme.{0}) (x : Sx (sch.obj X) p U) :
      ev (0 : Cochain ((chains R).obj (sch.obj X)) I j) p s h U x = 0 := by
    change Sec.map ((chainsXIso R (sch.obj X) p).inv ≫
      (0 : Cochain ((chains R).obj (sch.obj X)) I j).v _ _ h) (freeGen R _ U x) = 0
    rw [Cochain.zero_v, comp_zero]
    rfl
  have ev_res {j : ℤ} (a : Cochain ((chains R).obj (sch.obj X)) I j)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + j = s) {V U : Scheme.{0}}
      (g : V ⟶ U) (x : Sx (sch.obj X) p U) :
      Sec.res g (ev a p s h U x) = ev a p s h V (x.res g) := by
    change Sec.res g (Sec.map ((chainsXIso R (sch.obj X) p).inv ≫ a.v _ _ h) (freeGen R _ U x)) = _
    rw [CupSpec.map_res, CupSpec.freeGen_res]
    rfl
  have ev_ext {j : ℤ} (a b : Cochain ((chains R).obj (sch.obj X)) I j)
      (h : ∀ p s h U x, ev a p s h U x = ev b p s h U x) : a = b := by
    ext p s hs : 1
    by_cases hp : p ≤ 0
    · obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = -(q : ℤ) := ⟨(-p).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R (sch.obj X) q).inv]
      exact CupSpec.free_ext _ _ (fun U x => h q s hs U x)
    · exact (CupSpec.isZero_chains (R := R) (sch.obj X) p (by omega)).eq_of_src _ _
  refine ⟨fun z hz => ?_, fun α => ?_⟩
  · obtain ⟨a, ha⟩ := ev_exists (j := n)
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
        erw [SchCls.ev_δ_sch hnk a U p (-((p + 1 : ℕ) : ℤ) + n) t (by omega) ht x, ha, ha]
        simp only [Nat.add_one_ne_zero, dite_eq_right, not_false_eq_true, map_zero, zero_add]
        split_ifs with he hp0
        · rfl
        · exact absurd (hp0 ▸ (⟨0, rfl⟩ : Even 0)) he
        · exact smul_zero _
    refine ⟨Cocycle.mk a k hnk hc, fun U x => ?_, fun p s h U x => ?_⟩
    · change ev a 0 n _ U x = _
      erw [ha]
      simp only [dite_eq_left, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, SchCls.map_id']
    · change ev a (p + 1) s h U x = 0
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
      refine ⟨ev β 0 m (by simp) X (𝟙 X), ?_⟩
      erw [← hβ, ev_δ_zero hmn β X m n (by simp) (by simp)]
    · rintro ⟨y, hy⟩
      obtain ⟨b, hb⟩ := ev_exists (j := m)
        (fun p s h U x => if hp : p = 0 then
          Sec.map (I.XIsoOfEq (show m = s by omega)).hom (Sec.res (x : U ⟶ X) y)
          else if Even p then 0 else (-k.negOnePow) • ev α.1 (p + 1) s (by omega) U x)
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
        erw [SchCls.ev_δ_sch hmn b U p (-((p + 1 : ℕ) : ℤ) + m) t (by omega) ht x, hb, hb]
        have hc := SchCls.ev_δ_sch hnk α.1 U (p + 1) (-((p + 1 : ℕ) : ℤ) + m) t (by omega) (by omega) x
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

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicProperties
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ClsBasic

variable {R : Type} [CommRing R]

theorem single_add' {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} {p q : ℤ}
    (f g : K.X p ⟶ L.X q) (n : ℤ) : Cochain.single (f + g) n = Cochain.single f n + Cochain.single g n := by
  ext p' q' h
  by_cases hp : p' = p
  · subst hp
    by_cases hq : q' = q
    · subst hq; simp
    · simp [Cochain.single_v_eq_zero' _ _ _ _ _ hq]
  · simp [Cochain.single_v_eq_zero _ _ _ _ _ hp]

theorem ofHom_comp_single {C : Type*} [Category C] [Preadditive C] {K K' L : CochainComplex C ℤ} {p q : ℤ}
    (g : K' ⟶ K) (f : K.X p ⟶ L.X q) (n : ℤ) :
    (Cochain.ofHom g).comp (Cochain.single f n) (zero_add n) = Cochain.single (g.f p ≫ f) n := by
  ext p' q' h
  rw [Cochain.comp_v _ _ (zero_add n) p' p' q' (add_zero p') h, Cochain.ofHom_v]
  by_cases hp : p' = p
  · subst hp
    by_cases hq : q' = q
    · subst hq; simp
    · simp [Cochain.single_v_eq_zero' _ _ _ _ _ hq]
  · simp [Cochain.single_v_eq_zero _ _ _ _ _ hp]

theorem resι_d (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  have h := (injectiveResolution F).ι'.comm 0 1
  have h0 : ((singleFunctor (Shv R) 0).obj F).d 0 1 = 0 := by simp
  rw [h0, zero_comp] at h
  change ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ (injectiveResolution F).ι'.f 0) ≫ (injectiveResolution F).cochainComplex.d 0 1 = 0
  erw [Category.assoc, h]
  rfl

theorem chains_d (E : Spc) (n : ℕ) :
    ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (chainsXIso R E (n + 1)).hom ≫ (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫
        (chainsXIso R E n).inv := by
  have h := HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := n + 1) (j := n) rfl rfl
  have h2 : ((chainsN R).obj E).d (n + 1) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ n
  rw [← h2]
  exact h

theorem chainsXIso_nat {E E' : Spc} (f : E' ⟶ E) (n : ℕ) :
    ((chains R).map f).f (-(n : ℤ)) ≫ (chainsXIso R E n).hom = (chainsXIso R E' n).hom ≫ (free R).map (f.app (op ⦋n⦌)) := by
  have h := HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl
  change (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(n : ℤ)) ≫ _ = _
  rw [h]
  simp only [chainsXIso]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem δ_cls {E : Spc} {F : Shv R} {n : ℕ} (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) :
    δ (n : ℤ) ((n + 1 : ℕ) : ℤ) (Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n) =
      (((n + 1 : ℕ) : ℤ)).negOnePow • Cochain.single (p := -((n + 1 : ℕ) : ℤ)) (q := 0)
        ((chainsXIso R E (n + 1)).hom ≫ cobd s ≫ resι R F) ((n + 1 : ℕ) : ℤ) := by
  rw [Cochain.δ_single _ (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; ring) (-((n + 1 : ℕ) : ℤ)) 1 (by push_cast; ring) rfl]
  rw [Category.assoc, Category.assoc, resι_d, comp_zero, comp_zero, Cochain.single_zero, zero_add]
  congr 2
  rw [chains_d, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  rw [← Category.assoc]
  congr 1
  rw [cobd, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.zsmul_comp]

end GlobalTheory.EtC.ClsBasic

open GlobalTheory.EtC.ClsBasic in
theorem GlobalTheory.EtC.isCls_basic : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ),
    (∀ s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F, cobd s = 0 → ∃ x : H R E F n, IsCls s x) ∧
    (∀ (s s' : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x x' : H R E F n),
      IsCls s x → IsCls s' x' → IsCls (s + s') (x + x')) ∧
    (∀ (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x x' : H R E F n),
      IsCls s x → IsCls s x' → x = x') ∧
    (∀ (t : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x : H R E F ((n + 1 : ℕ) : ℤ)),
      IsCls (cobd t) x → x = 0) ∧
    ∀ (E' : Spc) (f : E' ⟶ E) (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x : H R E F n),
      IsCls s x → IsCls ((free R).map (f.app (op ⦋n⦌)) ≫ s) (pull R f F n x) := by
  intro R _ F E n
  refine ⟨fun s hs => ?_, fun s s' x x' hx hx' => ?_, fun s x x' hx hx' => ?_, fun t x hx => ?_, fun E' f s x hx => ?_⟩
  · refine ⟨CohomologyClass.mk (Cocycle.mk (Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n)
      ((n + 1 : ℕ) : ℤ) (by push_cast; ring) ?_), _, rfl, rfl⟩
    rw [ClsBasic.δ_cls, hs, zero_comp, comp_zero, Cochain.single_zero, smul_zero]
  · obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hx'
    refine ⟨z + z', (CohomologyClass.mk_add z z').symm, ?_⟩
    change z.1 + z'.1 = _
    rw [hz, hz', ← ClsBasic.single_add', Preadditive.add_comp, Preadditive.comp_add]
  · obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hx'
    have : z = z' := Cocycle.ext (hz.trans hz'.symm)
    rw [this]
  · obtain ⟨z, rfl, hz⟩ := hx
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n : ℤ) (by push_cast; ring)]
    refine ⟨(((n + 1 : ℕ) : ℤ)).negOnePow • Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ t ≫ resι R F) n, ?_⟩
    rw [δ_units_smul, ClsBasic.δ_cls, smul_smul, Int.units_mul_self, one_smul, hz]
  · obtain ⟨z, rfl, hz⟩ := hx
    refine ⟨zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add _), rfl, ?_⟩
    change (Cochain.ofHom ((chains R).map f)).comp z.1 (zero_add _) = _
    rw [hz, ClsBasic.ofHom_comp_single, ← Category.assoc, ClsBasic.chainsXIso_nat]
    simp only [Category.assoc]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceSectionHaarDecomposition
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem indicator_slice_orbit_isLocallyConstant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (K : Subgroup (GL (Fin a) k)), IsOpen (K : Set (GL (Fin a) k)) → K ≤ KO k (Fin a) →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a ↔ ∃ J, minor Y J ≠ 0) →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice (k := k) a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice (k := k) a d → g.val * Z ∈ slice (k := k) a d → g = 1) →
    IsLocallyConstant (Set.indicator {Y : Matrix (Fin a) (Fin d) k | ∃ x ∈ K, ∃ Z ∈ slice (k := k) a d, Y = x.val * Z}
      (1 : Matrix (Fin a) (Fin d) k → ℂ)) := by
  intro k _ _ _ _ a d K hKo hKO hrank s hs hsec huniq
  set T : Set (Matrix (Fin a) (Fin d) k) := {Y | ∃ x ∈ K, ∃ Z ∈ slice (k := k) a d, Y = x.val * Z} with hTdef
  set O : Set (Matrix (Fin a) (Fin d) k) := {Y | Y.rank = a} with hOdef
  have hmc : ∀ J : Fin a ↪ Fin d, Continuous fun Y : Matrix (Fin a) (Fin d) k => minor Y J := fun J => by
    unfold minor
    exact (continuous_id.matrix_submatrix id J).matrix_det

  have hT : ∀ Y ∈ O, (Y ∈ T ↔ s Y ∈ K) := by
    intro Y hY
    constructor
    · rintro ⟨x, hx, Z, hZ, rfl⟩
      have h1 : ((s (x.val * Z))⁻¹ * x).val * Z ∈ slice (k := k) a d := by
        rw [Units.val_mul, Matrix.mul_assoc]; exact hsec _ hY
      have h2 := huniq Z _ hZ h1
      have h3 : x = s (x.val * Z) := by
        have := congrArg (fun g => s (x.val * Z) * g) h2
        simpa [← mul_assoc] using this
      rw [← h3]; exact hx
    · intro h
      refine ⟨s Y, h, _, hsec Y hY, ?_⟩
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hTmin : ∀ Y ∈ T, ∃ J, valuation k (minor Y J) = 1 := by
    rintro Y ⟨x, hx, Z, ⟨J, hJ, -⟩, rfl⟩
    refine ⟨J, ?_⟩
    rw [minor_mul, minor, hJ, Matrix.det_one, mul_one]
    have := valuation_gdet_of_mem_KO (hKO hx)
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  have hTO : T ⊆ O := by
    intro Y hY
    obtain ⟨J, hJ⟩ := hTmin Y hY
    refine (hrank Y).2 ⟨J, fun h => ?_⟩
    rw [h, map_zero] at hJ
    exact zero_ne_one hJ
  have hOopen : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro Y hY
    obtain ⟨J, hJ⟩ := (hrank Y).1 hY
    have hv : valuation k (minor Y J) ≠ 0 := by simpa using hJ
    have hn := (valuation k).locally_const hv
    have := (hmc J).continuousAt.preimage_mem_nhds hn
    refine Filter.mem_of_superset this fun Y' hY' => (hrank Y').2 ⟨J, fun h0 => ?_⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq, h0, map_zero] at hY'
    exact hv hY'.symm
  have hKc : IsClosed (K : Set (GL (Fin a) k)) := Subgroup.isClosed_of_isOpen K hKo
  have hTeq : T = O ∩ s ⁻¹' (K : Set (GL (Fin a) k)) := by
    ext Y
    constructor
    · intro h; exact ⟨hTO h, (hT Y (hTO h)).1 h⟩
    · rintro ⟨h1, h2⟩; exact (hT Y h1).2 h2
  have hTopen : IsOpen T := by
    rw [hTeq]; exact hs.isOpen_inter_preimage hOopen hKo
  have h0 : {x : k | valuation k x < 1} ∈ nhds (0 : k) := by
    have := (IsValuativeTopology.hasBasis_nhds_zero k).mem_of_mem (i := 1) trivial
    simpa using this
  have hTclosed : IsClosed T := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro Y hY
    by_cases hYO : Y ∈ O
    · have hsY : s Y ∉ K := fun h => hY ((hT Y hYO).2 h)
      have ho : IsOpen (O ∩ s ⁻¹' (K : Set (GL (Fin a) k))ᶜ) := hs.isOpen_inter_preimage hOopen hKc.isOpen_compl
      refine Filter.mem_of_superset (ho.mem_nhds ⟨hYO, hsY⟩) fun Y' hY' hT' => hY'.2 ?_
      exact (hT Y' hY'.1).1 hT'
    · have hz : ∀ J, minor Y J = 0 := by
        intro J; by_contra hne; exact hYO ((hrank Y).2 ⟨J, hne⟩)
      have hW : (⋂ J : Fin a ↪ Fin d, (fun Y' => minor Y' J) ⁻¹' {x : k | valuation k x < 1}) ∈ nhds Y := by
        refine Filter.iInter_mem.2 fun J => ?_
        refine (hmc J).continuousAt.preimage_mem_nhds ?_
        rw [hz J]; exact h0
      refine Filter.mem_of_superset hW fun Y' hY' hT' => ?_
      obtain ⟨J, hJ⟩ := hTmin Y' hT'
      have := Set.mem_iInter.1 hY' J
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hJ] at this
      exact lt_irrefl _ this
  exact (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hTclosed, hTopen⟩).isLocallyConstant

end GlobalTheory.RankFibreKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecPiCofanIsColimitOfRingEquiv
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem spec_pi_cofan_isColimit : ∀ (ι : Type) [Finite ι] (T : ι → Type) [∀ i, CommRing (T i)] (B : Type) [CommRing B] (e : B ≃+* (∀ i, T i)), Nonempty (IsColimit (Cofan.mk (Spec (CommRingCat.of B)) (fun i => Spec.map (CommRingCat.ofHom ((Pi.evalRingHom T i).comp e.toRingHom))))) := by
  intro ι _ T _ B _ e
  let R : ι → CommRingCat := fun i => CommRingCat.of (T i)
  let eB : CommRingCat.of B ≅ CommRingCat.of (∀ i, T i) := e.toCommRingCatIso
  let φ : (∐ fun i => Spec (R i)) ≅ Spec (CommRingCat.of B) :=
    asIso (sigmaSpec R) ≪≫ Scheme.Spec.mapIso eB.op
  refine ⟨IsColimit.ofIsoColimit (coproductIsCoproduct _) (Cofan.ext φ ?_)⟩
  intro i
  simp only [φ, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.op_hom, Cofan.inj, Cofan.mk_ι_app]
  erw [ι_sigmaSpec_assoc]
  simp only [Scheme.Spec_map, Quiver.Hom.unop_op, ← Spec.map_comp]
  rfl

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorExistsPointFiniteSeparableStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zmodTorsor_exists_point_finite_separable : ∀ (B K : Type) [CommRing B] [Field K] (f : B →+* K) (D : Type) [CommRing D] [Algebra B D]
    (q : ℕ), 0 < q → ∀ (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor B D q act →
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (_ : Algebra.IsSeparable K L)
      (σ : D →+* L), σ.comp (algebraMap B D) = (algebraMap K L).comp f := by
  first | (exact @GlobalTheory.TorsorFieldPoint.exists_point_finite_separable) | (exact GlobalTheory.TorsorFieldPoint.exists_point_finite_separable) | (intros; apply GlobalTheory.TorsorFieldPoint.exists_point_finite_separable  <;> assumption)
end

