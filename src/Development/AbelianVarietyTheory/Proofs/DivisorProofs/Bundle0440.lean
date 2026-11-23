module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0424
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassEqZeroOfUnitTrivialization
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ChartChern
open CochainComplex CochainComplex.HomComplex GlobalTheory.EtC.ClsSpec GlobalTheory.EtC.ChernSpec

set_option backward.isDefEq.respectTransparency false

theorem firstChernClass_eq_zero_of_unit_trivialization (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : Inv q E)
    (s : ∀ U : Scheme.{0}, Sx E 0 U → (Γ(U, ⊤))ˣ)
    (hs : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 0 U), s V (x.res g) = umap g (s U x))
    (hL : ∀ (U : Scheme.{0}) (x : Sx E 1 U), s U (x.face 1) = lineUnit L x * s U (x.face 0)) :
    c1 q L = 0 := by
  obtain ⟨γ, hγ, h0, h1, h2s⟩ := firstChernClassTateTwist_cocycle_representative q hE L
  have h2 := face_forms q L γ.1 h2s
  have hq0 : ∀ (U : Scheme.{0}) (_ : Sx E 0 U), IsUnit (q : Γ(U, ⊤)) := fun U x ↦ hE U ⟨x⟩
  have e2 : (2 : ℤ).negOnePow = 1 := Int.negOnePow_even 2 even_two
  rw [← hγ, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff γ 1 (by norm_num)]
  rcases kumT_cases q with ht | ht
  ·
    obtain ⟨a, ha_res, ha_d, ha⟩ := exists_d_family ht (p := 0) hq0 s hs
    obtain ⟨b, hb_res, hb⟩ := exists_two_family ht (p := 1) (fun U y ↦ hq0 U (y.face 0))
      (fun U y ↦ lineUnit L y) (fun U y ↦ s U (y.face 0)) (fun V U g y ↦ lineUnit_res L g y)
      (fun V U g y ↦ by rw [← face_res, hs])
    obtain ⟨β₀, hβ₀, hβ₀'⟩ := exists_single (E := E) (I := res _ (tw q 1)) (n := 1) 0 1 (by simp)
      (fun U x ↦ -a U x) (fun V U g x ↦ by rw [← ha_res]; exact map_neg _ _)
    obtain ⟨β₁, hβ₁, hβ₁'⟩ := exists_single (E := E) (I := res _ (tw q 1)) (n := 1) 1 0 (by simp)
      b hb_res
    have K0 : ∀ (U : Scheme.{0}) (x : Sx E 0 U),
        ev (δ 1 2 (β₀ + β₁)) 0 2 (by simp) U x = ev γ.1 0 2 (by simp) U x := by
      intro U x
      rw [CupSpec.ev_δ_zero (by norm_num) _ U 1 2 (by simp) (by simp) x, h0, ClsSpec.ev_add, hβ₀,
        hβ₁' 0 1 (by simp) U x (by norm_num), add_zero]
      have hd := ha_d U x
      simp only [Sec.map] at hd ⊢
      rw [map_neg, hd, neg_zero]
    have K1' : ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
        w ^ q = s U (x.face 0) →
        ev (δ 1 2 (β₀ + β₁)) 1 1 (by simp) U x = ev γ.1 1 1 (by simp) U x := by
      intro U x v w hv hw
      have hvw : (v * w) ^ q = s U (x.face 1) := by rw [mul_pow, hv, hw, hL]
      rw [CupSpec.ev_δ_succ (by norm_num) _ U 0 0 1 (by simp) (by simp) x, h1 U x v hv,
        ClsSpec.ev_add, hβ₀' 1 0 (by simp) U x (by norm_num), hβ₁, smap_add, smap_zero, zero_add]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, ClsSpec.ev_add, hβ₀, hβ₁',
        Fin.succ_zero_eq_one, ne_eq, zero_ne_one, not_false_eq_true]
      rw [hb U x v w hv hw, ha U _ w hw, ha U _ (v * w) hvw, e2]
      simp only [smap_add, smap_sub, add_zero, one_smul, Fin.val_zero, Fin.val_one,
        pow_zero, pow_one, neg_smul, neg_neg]
      abel
    have K1 : ∀ (U : Scheme.{0}) (x : Sx E 1 U),
        ev (δ 1 2 (β₀ + β₁)) 1 1 (by simp) U x = ev γ.1 1 1 (by simp) U x := by
      intro U x
      apply ClsSpec.sep
      refine ClsSpec.loc_mono (ClsSpec.loc_and (root_loc (hq0 U (x.face 0)) (lineUnit L x))
        (root_loc (hq0 U (x.face 0)) (s U (x.face 0)))) ?_
      rintro V g ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
      rw [CupSpec.ev_res, CupSpec.ev_res]
      exact K1' V (x.res g) v w (by rw [hv, lineUnit_res]) (by rw [hw, ← face_res, hs])
    have K2' : ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w z : (Γ(U, ⊤))ˣ),
        v ^ q = lineUnit L (x.face 2) → w ^ q = lineUnit L (x.face 0) →
        z ^ q = s U ((x.face 0).face 0) →
        ev (δ 1 2 (β₀ + β₁)) 2 0 (by simp) U x = ev γ.1 2 0 (by simp) U x := by
      intro U x v w z hv hw hz
      have f10 : (x.face 1).face 0 = (x.face 0).face 0 :=
        face_face x 1 0 0 0 (SimplexCategory.δ_comp_δ (i := 0) (j := 0) le_rfl)
      have f20 : (x.face 2).face 0 = (x.face 0).face 1 :=
        face_face x 2 0 0 1 (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide))
      have hvw : (v * w) ^ q = lineUnit L (x.face 1) := by rw [mul_pow, hv, hw, lineUnit_face]
      have hz1 : z ^ q = s U ((x.face 1).face 0) := by rw [f10, hz]
      have hwz : (w * z) ^ q = s U ((x.face 2).face 0) := by rw [mul_pow, hw, hz, f20, hL]
      rw [CupSpec.ev_δ_succ (by norm_num) _ U 1 (-1) 0 (by simp) (by simp) x, h2 U x v w hv hw]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, ClsSpec.ev_add, hβ₀', hβ₁,
        Fin.succ_zero_eq_one, Fin.succ_one_eq_two, ne_eq, one_ne_zero, not_false_eq_true]
      rw [hb U _ w z hw hz, hb U _ (v * w) z hvw hz1, hb U _ v (w * z) hv hwz, e2, mul_assoc]
      simp only [zero_add, add_zero, one_smul, Fin.val_zero, Fin.val_one, Fin.val_two,
        pow_zero, pow_one, neg_smul]
      simp only [even_two, Even.neg_one_pow, one_smul]
      rw [hβ₀' 2 (-1) (by simp) U x (by norm_num), hβ₁' 2 (-1) (by simp) U x (by norm_num), add_zero,
        smap_zero, zero_add]
      abel
    have K2 : ∀ (U : Scheme.{0}) (x : Sx E 2 U),
        ev (δ 1 2 (β₀ + β₁)) 2 0 (by simp) U x = ev γ.1 2 0 (by simp) U x := by
      intro U x
      have hU := hq0 U ((x.face 0).face 0)
      apply ClsSpec.sep
      refine ClsSpec.loc_mono (ClsSpec.loc_and (ClsSpec.loc_and (root_loc hU (lineUnit L (x.face 2)))
        (root_loc hU (lineUnit L (x.face 0)))) (root_loc hU (s U ((x.face 0).face 0)))) ?_
      rintro V g ⟨⟨⟨v, hv⟩, ⟨w, hw⟩⟩, ⟨z, hz⟩⟩
      rw [CupSpec.ev_res, CupSpec.ev_res]
      exact K2' V (x.res g) v w z (by rw [hv, ← face_res, lineUnit_res])
        (by rw [hw, ← face_res, lineUnit_res]) (by rw [hz, ← face_res, ← face_res, hs])
    refine ⟨β₀ + β₁, CupSpec.ev_ext _ _ fun p t ht' U x ↦ ?_⟩
    rcases p with _ | _ | _ | p
    · obtain rfl : t = 2 := by omega
      exact K0 U x
    · obtain rfl : t = 1 := by omega
      exact K1 U x
    · obtain rfl : t = 0 := by omega
      exact K2 U x
    · exact ChernSpec.sec_neg _ t (by omega) _ _
  ·
    have Z1 : ∀ (U : Scheme.{0}) (x : Sx E 1 U), (0 : Sec ((res _ (tw q 1)).X 1) U) =
        ev γ.1 1 1 (by simp) U x := by
      intro U x
      apply ClsSpec.sep
      refine ClsSpec.loc_mono (root_loc (hq0 U (x.face 0)) (lineUnit L x)) ?_
      rintro V g ⟨v, hv⟩
      rw [CupSpec.ev_res, res_zero, h1 V (x.res g) v (by rw [hv, lineUnit_res]), ht]
      simp only [Pi.zero_apply, smap_zero]
    have Z2 : ∀ (U : Scheme.{0}) (x : Sx E 2 U), (0 : Sec ((res _ (tw q 1)).X 0) U) =
        ev γ.1 2 0 (by simp) U x := by
      intro U x
      have hU := hq0 U ((x.face 0).face 0)
      apply ClsSpec.sep
      refine ClsSpec.loc_mono (ClsSpec.loc_and (root_loc hU (lineUnit L (x.face 2)))
        (root_loc hU (lineUnit L (x.face 0)))) ?_
      rintro V g ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
      rw [CupSpec.ev_res, res_zero, h2 V (x.res g) v w (by rw [hv, ← face_res, lineUnit_res])
        (by rw [hw, ← face_res, lineUnit_res]), ht]
      simp only [Pi.zero_apply, add_zero, sub_zero]
    refine ⟨0, ?_⟩
    rw [δ_zero]
    refine CupSpec.ev_ext _ _ fun p t ht' U x ↦ ?_
    rw [CupSpec.ev_zero]
    rcases p with _ | _ | _ | p
    · obtain rfl : t = 2 := by omega
      exact (h0 U x).symm
    · obtain rfl : t = 1 := by omega
      exact Z1 U x
    · obtain rfl : t = 0 := by omega
      exact Z2 U x
    · exact ChernSpec.sec_neg _ t (by omega) _ _

end GlobalTheory.EtC.ChartChern

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddiStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

open GlobalTheory.EtC.ClsSpec in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive :
    ∀ (q : ℕ) [NeZero q],
      (∀ {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
        ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2,
          CohomologyClass.mk γ = c1 q L ∧
          (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := ZMod q) γ.1 0 2 (by simp) U x = 0) ∧
          (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
            ev (R := ZMod q) γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
          ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ),
            v ^ q = lineUnit L (x.sub 0 1 (by omega)) → w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
            ev (R := ZMod q) γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) ∧
      (∀ {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)), Inv q E' →
        pull _ f _ _ (c1 q L) = c1 q (f ≫ L)) ∧
      ∀ {E : Spc} (L M N : E ⟶ ofCat (glCat 1)), Inv q E →
        (∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) →
        c1 q N = c1 q L + c1 q M := by
  intro q _
  refine ⟨?_, fun f L hE => ChernSpec.firstChernClassTateTwist_pullback q f L hE,
    fun L M N hE hN => ChernSpec.isOneCochain_add q L M N hE hN⟩
  have exists_single {E : Spc} {I : Cx (ZMod q)} {n : ℤ} (p₀ : ℕ) (s₀ : ℤ) (h₀ : -(p₀ : ℤ) + n = s₀)
      (b : ∀ U : Scheme.{0}, Sx E p₀ U → Sec (I.X s₀) U)
      (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p₀ U), Sec.res g (b U x) = b V (x.res g)) :
      ∃ α : Cochain ((chains (ZMod q)).obj E) I n, (∀ U x, ev (R := ZMod q) α p₀ s₀ h₀ U x = b U x) ∧
        ∀ p s h U x, p ≠ p₀ → ev (R := ZMod q) α p s h U x = 0 := by
    subst h₀
    obtain ⟨α, hα⟩ := exists_cochain_ev_eq_of_natural (ZMod q) (E := E) (I := I) (n := n)
      (fun p s h U x => if hp : p = p₀ then (by subst hp; subst h; exact b U x) else 0) (by
        intro p s h V U g x
        by_cases hp : p = p₀
        · subst hp; subst h
          simp only [dite_eq_left]
          exact hb V U g x
        · simp only [dite_eq_right hp]
          exact map_zero _)
    refine ⟨α, fun U x => ?_, fun p s h U x hp => ?_⟩
    · rw [hα]
      simp only [dite_eq_left]
    · rw [hα]
      simp only [dite_eq_right hp]
  have differential_eq_zero {E : Spc} {I : Cx (ZMod q)} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains (ZMod q)).obj E) I n)
      (h₀ : ∀ (U : Scheme.{0}) (x : Sx E 0 U), Sec.map (I.d n m) (ev (R := ZMod q) α 0 n (by simp) U x) = 0)
      (h₁ : ∀ (U : Scheme.{0}) (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -(p : ℤ) + n = t) (x : Sx E (p + 1) U),
        Sec.map (I.d s t) (ev (R := ZMod q) α (p + 1) s hs U x) +
          m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev (R := ZMod q) α p t ht U (x.face i) = 0) : δ n m α = 0 := by
    refine CupSpec.ev_ext _ _ fun p t ht U x => ?_
    rw [CupSpec.ev_zero]
    cases p with
    | zero =>
      obtain rfl : m = t := by simpa using ht
      exact (CupSpec.ev_δ_zero hm α U n m (by simp) (by simp) x).trans (h₀ U x)
    | succ p => exact (CupSpec.ev_δ_succ hm α U p _ t rfl ht x).trans (h₁ U p _ t rfl _ x)
  have exists_cocycle {t : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec ((res _ (tw q 1)).X 0) U} (ht : IsKum q t)
      {E : Spc} (hE : Inv q E) (L : E ⟶ ofCat (glCat 1)) :
      ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2,
      (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := ZMod q) γ.1 0 2 (by simp) U x = 0) ∧
      (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
        ev (R := ZMod q) γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (t U v)) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
        w ^ q = lineUnit L (x.face 0) →
        ev (R := ZMod q) γ.1 2 0 (by simp) U x = t U v + t U w - t U (v * w) := by
    have hq₁ : ∀ (U : Scheme.{0}) (_ : Sx E 1 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hE U ⟨x.face 0⟩
    have hq₂ : ∀ (U : Scheme.{0}) (_ : Sx E 2 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hq₁ U (x.face 0)
    have hf : ∀ (i : Fin 3) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 2 U),
        lineUnit L ((x.res g).face i) = umap g (lineUnit L (x.face i)) := fun i _ _ g x => ChernSpec.lineUnit_face_res L g x i
    obtain ⟨b, hb, hd, hv⟩ := exists_d_family ht hq₁ (fun U x => lineUnit L x) (fun V U g x => lineUnit_res L g x)
    obtain ⟨e, he, hw⟩ := exists_two_family ht hq₂ (fun U x => lineUnit L (x.face 2)) (fun U x => lineUnit L (x.face 0))
      (hf 2) (hf 0)
    have h₂ : ∀ (U : Scheme.{0}) (y : Sx E 2 U),
        Sec.map ((res _ (tw q 1)).d 0 1) (e U y) = b U (y.face 0) - b U (y.face 1) + b U (y.face 2) := by
      intro U y
      refine sep (loc_mono (loc_and (root_loc (hq₂ U y) (lineUnit L (y.face 2))) (root_loc (hq₂ U y) (lineUnit L (y.face 0)))) ?_)
      rintro V g ⟨⟨v, h⟩, w, h'⟩
      rw [← hf] at h h'
      rw [res_map, res_add, res_sub, he, hb, hb, hb, face_res, face_res, face_res, hw V _ v w h h', hv V _ v h, hv V _ w h',
        hv V _ (v * w) (by rw [mul_pow, h, h', lineUnit_face]), smap_sub, smap_add]
      abel
    have h₃ : ∀ (U : Scheme.{0}) (y : Sx E 3 U),
        e U (y.face 0) - e U (y.face 1) + e U (y.face 2) - e U (y.face 3) = 0 := by
      intro U y
      have hU := hq₂ U (y.face 0)
      refine sep (loc_mono (loc_and (root_loc hU (lineUnit L ((y.face 3).face 2)))
        (loc_and (root_loc hU (lineUnit L ((y.face 0).face 2))) (root_loc hU (lineUnit L ((y.face 0).face 0))))) ?_)
      rintro V g ⟨⟨u, h⟩, ⟨v, h'⟩, w, h''⟩
      rw [← hf, face_res] at h h' h''
      rw [res_sub, res_add, res_sub, he, he, he, he, face_res, face_res, face_res, face_res, res_zero]
      generalize y.res g = z at h h' h'' ⊢
      have e₁ : (z.face 1).face 0 = (z.face 0).face 0 := face_face z _ _ _ _ (by decide)
      have e₂ : (z.face 1).face 2 = (z.face 3).face 1 := face_face z _ _ _ _ (by decide)
      have e₃ : (z.face 2).face 2 = (z.face 3).face 2 := face_face z _ _ _ _ (by decide)
      have e₄ : (z.face 2).face 0 = (z.face 0).face 1 := face_face z _ _ _ _ (by decide)
      have e₅ : (z.face 3).face 0 = (z.face 0).face 2 := face_face z _ _ _ _ (by decide)
      rw [hw V _ v w h' h'', hw V (z.face 1) (u * v) w (by rw [e₂, lineUnit_face, e₅, mul_pow, h, h']) (by rw [e₁, h'']),
        hw V (z.face 2) u (v * w) (by rw [e₃, h]) (by rw [e₄, lineUnit_face, mul_pow, h', h'']),
        hw V (z.face 3) u v h (by rw [e₅, h']), mul_assoc]
      abel
    obtain ⟨α, a₁, a₂⟩ := exists_single (I := res _ (tw q 1)) (n := 2) 1 1 (by simp) b hb
    obtain ⟨β, b₁, b₂⟩ := exists_single (I := res _ (tw q 1)) (n := 2) 2 0 (by simp) e he
    have c₀ : ∀ p s h U x, p ≠ 1 → p ≠ 2 → ev (R := ZMod q) (α + β) p s h U x = 0 := fun p s h U x h₁ h₂ => by
      rw [CupSpec.ev_add, a₂ _ _ _ _ _ h₁, b₂ _ _ _ _ _ h₂, add_zero]
    have c₁ : ∀ h U x, ev (R := ZMod q) (α + β) 1 1 h U x = b U x := fun h U x => by
      rw [CupSpec.ev_add, a₁, b₂ _ _ _ _ _ (by decide), add_zero]
    have c₂ : ∀ h U x, ev (R := ZMod q) (α + β) 2 0 h U x = e U x := fun h U x => by
      rw [CupSpec.ev_add, b₁, a₂ _ _ _ _ _ (by decide), zero_add]
    have hs : (3 : ℤ).negOnePow = -1 := rfl
    refine ⟨Cocycle.mk (α + β) 3 rfl (differential_eq_zero (m := 3) rfl _ (fun U x => ?_) (fun U p s t hs' ht' x => ?_)),
      fun U x => c₀ 0 2 _ U x (by decide) (by decide), fun U x v h => (c₁ _ U x).trans (hv U x v h),
      fun U x v w h h' => (c₂ _ U x).trans (hw U x v w h h')⟩
    · rw [c₀ _ _ _ _ _ (by decide) (by decide), smap_zero]
    · match p with
      | 0 =>
        obtain rfl : s = 1 := by omega
        obtain rfl : t = 2 := by omega
        rw [Finset.sum_eq_zero fun i _ => by rw [c₀ _ _ _ _ _ (by decide) (by decide), smul_zero], smul_zero, add_zero]
        exact (congrArg _ (c₁ _ U x)).trans (hd U x)
      | 1 =>
        obtain rfl : s = 0 := by omega
        obtain rfl : t = 1 := by omega
        rw [Fin.sum_univ_three, c₁, c₁, c₁, c₂, h₂, hs]
        simp
        abel
      | 2 =>
        obtain rfl : t = 0 := by omega
        rw [Fin.sum_univ_four, c₂, c₂, c₂, c₂, c₀ _ _ _ _ _ (by decide) (by decide), smap_zero, zero_add]
        convert smul_zero _
        rw [← h₃ U x]
        norm_num
        abel
      | p + 3 =>
        rw [c₀ _ _ _ _ _ (by omega) (by omega), smap_zero, zero_add,
          Finset.sum_eq_zero fun i _ => by rw [c₀ _ _ _ _ _ (by omega) (by omega), smul_zero], smul_zero]
  intro E L hE
  refine pick_spec (P := fun c : Ht q E 2 1 => ∃ γ : Cocycle _ _ 2, CohomologyClass.mk γ = c ∧
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := ZMod q) γ.1 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev (R := ZMod q) γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev (R := ZMod q) γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) ?_
  rcases kumT_cases q with h | h
  · obtain ⟨γ, h₀, h₁, h₂⟩ := exists_cocycle h hE L
    exact ⟨_, γ, rfl, h₀, h₁, fun U x v w hv hw => h₂ U x v w (by rw [hv, sub_zero_one]) (by rw [hw, sub_one_one])⟩
  · refine ⟨_, 0, rfl, fun U x => CupSpec.ev_zero _ _ _ _ _, fun U x v _ => (CupSpec.ev_zero _ _ _ _ _).trans ?_,
      fun U x v w _ _ => (CupSpec.ev_zero _ _ _ _ _).trans ?_⟩
    · rw [h]
      exact (smap_zero _).symm
    · rw [h]
      simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthEqZeroOfLtPrime
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem val_natCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℕ) :
    0 ≤ v (n : C) := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (le_min ih (le_of_eq (AddValuation.map_one v).symm)).trans (AddValuation.map_add v _ _)

theorem val_intCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℤ) :
    0 ≤ v (n : C) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [Int.cast_natCast]
    exact val_natCast_nonneg v m
  · rw [Int.cast_neg, AddValuation.map_neg, Int.cast_natCast]
    exact val_natCast_nonneg v m

theorem val_natCast_eq_zero {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (p : ℕ)
    (hp : p.Prime) (hv : v (p : C) = 1) (n : ℕ) (hn : ¬ p ∣ n) : v (n : C) = 0 := by
  have h0 := val_natCast_nonneg v n
  refine le_antisymm ?_ h0
  by_contra hlt
  rw [not_le] at hlt
  have hb := Nat.gcd_eq_gcd_ab p n
  rw [((Nat.Prime.coprime_iff_not_dvd hp).2 hn).gcd_eq_one, Nat.cast_one] at hb
  have key : (1 : C) = (p : C) * (Nat.gcdA p n : C) + (n : C) * (Nat.gcdB p n : C) := by
    have := congrArg (fun z : ℤ => (z : C)) hb
    push_cast at this
    exact this
  have one_pos' : (0 : WithTop ℝ) < 1 := by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)
  have h1 : 0 < v ((p : C) * (Nat.gcdA p n : C)) := by
    rw [AddValuation.map_mul, hv]
    exact add_pos_of_pos_of_nonneg one_pos' (val_intCast_nonneg v _)
  have h2 : 0 < v ((n : C) * (Nat.gcdB p n : C)) := by
    rw [AddValuation.map_mul]
    exact add_pos_of_pos_of_nonneg hlt (val_intCast_nonneg v _)
  have hsum := AddValuation.map_add v ((p : C) * (Nat.gcdA p n : C)) ((n : C) * (Nat.gcdB p n : C))
  rw [← key, AddValuation.map_one] at hsum
  exact absurd hsum (not_le.2 (lt_min h1 h2))

end GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem detDepth_eq_zero_of_lt : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C), IsSatFrame v u → c < p → detDepth G u c = 0 := by
  intro C _ _ v p hp hv i d c G u hu hc
  obtain ⟨hlo, hcont, -⟩ := _root_.GlobalTheory.FGDepth.detDepth_bounds C v p hp hv i d c G u hu
  obtain ⟨-, -, hone, hrow⟩ := _root_.GlobalTheory.DetPowShape.detPow_shape C i c
  set α₀ : (Σ _ : Fin i, Fin i) →₀ ℕ := ∑ a : Fin i, Finsupp.single ⟨a, a⟩ c with hα₀
  have hmem : α₀ ∈ (detPow C i c).support := by
    rw [MvPolynomial.mem_support_iff, hone]
    exact one_ne_zero
  have hfact : v (mfact α₀ : C) = 0 := by
    have hcast : (mfact α₀ : C) = ((α₀.prod fun _ n => n.factorial : ℕ) : C) := by
      unfold mfact
      rw [Nat.cast_finsuppProd]
    rw [hcast]
    apply val_natCast_eq_zero v p hp hv
    intro hdvd
    rw [Finsupp.prod] at hdvd
    obtain ⟨x, -, hx⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
    rw [hp.dvd_factorial] at hx
    obtain ⟨b, a⟩ := x
    have hle : α₀ ⟨b, a⟩ ≤ c := by
      rw [← (hrow α₀ hmem).1 a]
      exact Finset.single_le_sum (f := fun b' => α₀ ⟨b', a⟩) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
    omega
  have hle : content v (detPow C i c) ≤ 0 := by
    unfold content
    refine (iInf₂_le α₀ hmem).trans (le_of_eq ?_)
    rw [hone, one_mul, hfact]
    rfl
  exact le_antisymm (hcont.trans hle) hlo

end GlobalTheory.FGDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafMapMonoEpiIsoStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso : ∀ (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q), (Mono f → Mono ((free R).map f)) ∧ ((∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, f.app (op V) x = Q.map g.op y) → Epi ((free R).map f)) ∧ ((∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, f.app (op V) x = Q.map g.op y) → (∀ U (x x' : P.obj (op U)), f.app (op U) x = f.app (op U) x' → Loc U fun _ g => P.map g.op x = P.map g.op x') → IsIso ((free R).map f)) := by
  first | (exact @GlobalTheory.EtC.free_map_mono_epi_iso) | (exact GlobalTheory.EtC.free_map_mono_epi_iso) | (intros; apply GlobalTheory.EtC.free_map_mono_epi_iso  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafPresheafOverCoproductEqSumStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeEtaleSheaf_presheaf_over_coproduct_eq_sum : ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → ∀ (P : PSh) (t : P ⟶ yoneda.obj U) (Q : ι → PSh) (a : ∀ i, Q i ⟶ P) (b : ∀ i, Q i ⟶ yoneda.obj (V i)), (∀ i, IsPullback (a i) (b i) t (yoneda.map (j i))) → Nonempty (IsColimit (Cofan.mk ((free R).obj P) (fun i => (free R).map (a i)))) := by
  first | (exact @GlobalTheory.EtC.FreeCofan.main) | (exact GlobalTheory.EtC.FreeCofan.main) | (intros; apply GlobalTheory.EtC.FreeCofan.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraProductCuspidalGLFrobeniusPowStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraProductCuspidalGL_frobenius_pow : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F ≃+* F) (j : ℕ), (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (L : List (ℕ × ℕ)) (n : ℕ) (x : GL (Fin n) F), J θ L n (gal (t : F →+* F) n x) = J θ (L.map fun p => (p.1, p.2 * ringChar F ^ j)) n x := by
  first | (exact @GlobalTheory.Shin.J_gal) | (exact GlobalTheory.Shin.J_gal) | (intros; apply GlobalTheory.Shin.J_gal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicRingClassLatticeOneEqOrder
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.HatCap

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_integral :
    IsOpen {y : Af E | ∀ v : HeightOneSpectrum (𝓞 E), y v ∈ v.adicCompletionIntegers E} :=
  RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (A := fun v : HeightOneSpectrum (𝓞 E) => (v.adicCompletionIntegers E : Set (v.adicCompletion E)))
    (fun v => Valued.isOpen_valuationSubring (v.adicCompletion E))

theorem mem_orderC_of_mem_hatO {c : Ideal (OF E)} (hc : c ≠ ⊥) {x : E} (hx : algebraMap E (Af E) x ∈ hatO c) :
    x ∈ orderC c := by
  obtain ⟨n, hnc, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  have hnE : algebraMap (OF E) E n ≠ 0 := by
    intro h
    apply hn0
    have h' : ((n : maximalRealSubfield E) : E) = 0 := h
    exact_mod_cast h'
  set m : E := algebraMap (OF E) E n with hm
  have hcont : Continuous fun z : Af E => (algebraMap E (Af E) x - z) * algebraMap E (Af E) m⁻¹ :=
    (continuous_const.sub continuous_id).mul continuous_const
  have hU := isOpen_integral.preimage hcont
  obtain ⟨_, hz, y, hy, rfl⟩ := mem_closure_iff.1 hx _ hU (by
    rw [Set.mem_preimage, sub_self, zero_mul]
    exact fun v => zero_mem _)
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = (x - y) * m⁻¹ := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ fun v => ?_
    have h3 : (algebraMap E (Af E) ((x - y) * m⁻¹)) v ∈ v.adicCompletionIntegers E := by
      rw [map_mul, map_sub]; exact hz v
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm.trans_le
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h3)
  have hxy : x = y + algebraMap (𝓞 E) E (b * algebraMap (OF E) (𝓞 E) n) := by
    have : algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) n) = m := rfl
    rw [map_mul, hb, this, mul_assoc, inv_mul_cancel₀ hnE]; ring
  rw [hxy]
  refine add_mem hy (mem_orderC.2 ⟨0, _, Ideal.mul_mem_left _ b (Ideal.mem_map_of_mem _ hnc), by simp⟩)

theorem lattice_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → lattice c 1 = (orderC c : Set E) := by
  intro E _ _ _ c hc
  ext x
  rw [mem_lattice, inv_one, Units.val_one, mul_one]
  exact ⟨mem_orderC_of_mem_hatO hc, algebraMap_mem_hatO⟩

end GlobalTheory.CMVal.HatCap
end
end

