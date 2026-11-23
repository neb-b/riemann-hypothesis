module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PThMuLat
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma det_form {S : Type} [CommRing S] [Algebra ℂ S] (R : Subalgebra ℂ S) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (P I : Finset (Fin n)) (f : Fin n → Fin n) (D : Fin n → S) (w : S)
    (t : Fin n → Fin n → S)
    (hP : ∀ a ∈ P, ∀ m, A a m = if m = f a then 1 else 0)
    (hI : ∀ a ∈ P, f a ∈ I)
    (hI' : ∀ m ∈ I, ∃ a ∈ P, f a = m)
    (hA : ∀ a, a ∉ P → ∀ m, m ∉ I → A a m = D m * w * t a m)
    (ht : ∀ a m, t a m ∈ R) :
    ∃ s ∈ R, A.det = s * (∏ m ∈ Iᶜ, D m) * w ^ (Pᶜ).card := by
  refine ⟨∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : S) *
      ((∏ a ∈ P, A a (σ a)) * ∏ a ∈ Pᶜ, t a (σ a)), ?_, ?_⟩
  · refine Subalgebra.sum_mem _ (fun σ _ => Subalgebra.mul_mem _ (intCast_mem R _)
      (Subalgebra.mul_mem _ (Subalgebra.prod_mem _ (fun a ha => ?_)) (Subalgebra.prod_mem _ (fun a _ => ht _ _))))
    rw [hP a ha]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  · rw [← Matrix.det_transpose, Matrix.det_apply', Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp only [Matrix.transpose_apply]
    rw [← Finset.prod_mul_prod_compl P]
    by_cases hσ : ∀ a ∈ P, σ a = f a
    · have hout : ∀ a ∉ P, σ a ∉ I := by
        intro a ha hm
        obtain ⟨b, hb, hfb⟩ := hI' _ hm
        have hba : σ b = σ a := by rw [hσ b hb, hfb]
        apply ha
        rw [← σ.injective hba]
        exact hb
      have hD : ∏ a ∈ Pᶜ, D (σ a) = ∏ m ∈ Iᶜ, D m := by
        refine Finset.prod_nbij σ (fun a ha => Finset.mem_compl.2 (hout a (Finset.mem_compl.1 ha)))
          (fun a _ b _ hab => σ.injective hab) ?_ (fun a _ => rfl)
        intro m hm
        have hm' : m ∉ I := Finset.mem_compl.1 hm
        refine ⟨σ.symm m, Finset.mem_coe.2 (Finset.mem_compl.2 (fun hp => ?_)), σ.apply_symm_apply m⟩
        have h1 := hσ _ hp
        rw [σ.apply_symm_apply] at h1
        exact hm' (h1 ▸ hI _ hp)
      have hprod : ∏ a ∈ Pᶜ, A a (σ a) = (∏ m ∈ Iᶜ, D m) * w ^ Pᶜ.card * ∏ a ∈ Pᶜ, t a (σ a) := by
        rw [Finset.prod_congr rfl (fun a ha => hA a (Finset.mem_compl.1 ha) (σ a) (hout a (Finset.mem_compl.1 ha)))]
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, hD]
      rw [hprod]
      ring
    · push_neg at hσ
      obtain ⟨a, ha, hne⟩ := hσ
      have h0 : ∏ a ∈ P, A a (σ a) = 0 := Finset.prod_eq_zero ha (by rw [hP a ha, if_neg hne])
      rw [h0]
      ring

theorem UpperTheory.Gal.productCup_of_system.thMuLat_of :
    ThMuLat := by
  unfold ThMuLat
  intro d S E _ _ _ _ T hT
  refine ⟨?_, ?_⟩
  · unfold Sys.admitted
    intro i j l
    have hx : ∀ a, ((T.X a * (T.X i)⁻¹ : Sˣ) : S) ∈ T.R {i} {j} := fun a =>
      hT.memX {i} {j} (Finset.singleton_nonempty j) i (Finset.mem_singleton_self i) a
    have hy : ∀ a, ((T.Y a * (T.Y j)⁻¹ : Sˣ) : S) ∈ T.R {i} {j} := fun a =>
      hT.memY {i} {j} (Finset.singleton_nonempty i) j (Finset.mem_singleton_self j) a
    have key := sub_mem (mul_mem (hx (ofLex l).1) (hy (ofLex l).2))
      (mul_mem (hx (ofLex l).2) (hy (ofLex l).1))
    simp only [Units.val_mul] at key
    convert key using 1
    simp only [Sys.r, Sys.u, Sys.mu, n11, pow_one, mul_inv, Units.val_mul]
    ring
  · intro I J L hI j hj
    unfold detC
    by_cases h : (uni I L).card = d + 1
    · classical
      rw [dite_eq_left h]
      set e := (uni I L).orderEmbOfFin h with he
      have mem_e : ∀ a, e a ∈ uni I L := fun a => Finset.orderEmbOfFin_mem _ h a
      have mem_l : ∀ i : Fin (d + 1), (toLex (Sum.inl i : Fin (d + 1) ⊕ Mi d) ∈ uni I L) ↔ i ∈ I := by
        intro i
        simp [uni]
      have inl_mem : ∀ a i, ofLex (e a) = Sum.inl i → i ∈ I := by
        intro a i hai
        have h2 : e a = toLex (Sum.inl i) := by rw [← hai]; rfl
        exact (mem_l i).1 (h2 ▸ mem_e a)
      obtain ⟨P, hPm⟩ : ∃ P : Finset (Fin (d + 1)), ∀ a, a ∈ P ↔ ∃ i, ofLex (e a) = Sum.inl i :=
        ⟨Finset.univ.filter fun a => ∃ i, ofLex (e a) = Sum.inl i, fun a => by simp⟩
      obtain ⟨f, hf⟩ : ∃ f : Fin (d + 1) → Fin (d + 1), ∀ a i, ofLex (e a) = Sum.inl i → f a = i :=
        ⟨fun a => Sum.elim id (fun _ => 0) (ofLex (e a)), fun a i hai => by simp [hai]⟩
      have hfI : ∀ a ∈ P, f a ∈ I := by
        intro a ha
        obtain ⟨i, hi⟩ := (hPm a).1 ha
        rw [hf a i hi]
        exact inl_mem a i hi
      have hIf : ∀ m ∈ I, ∃ a ∈ P, f a = m := by
        intro m hm
        have hr : toLex (Sum.inl m : Fin (d + 1) ⊕ Mi d) ∈ Set.range e := by
          rw [he, Finset.range_orderEmbOfFin]
          exact (mem_l m).2 hm
        obtain ⟨a, ha⟩ := hr
        have ha' : ofLex (e a) = Sum.inl m := by rw [ha]; rfl
        exact ⟨a, (hPm a).2 ⟨m, ha'⟩, hf a m ha'⟩
      have hPcard : P.card = I.card := by
        refine Finset.card_nbij f hfI ?_ (fun m hm => ?_)
        · intro a ha b hb hab
          obtain ⟨i, hi⟩ := (hPm a).1 ha
          obtain ⟨i', hi'⟩ := (hPm b).1 hb
          rw [hf a i hi, hf b i' hi'] at hab
          apply e.injective
          have h1 : e a = toLex (Sum.inl i) := by rw [← hi]; rfl
          have h2 : e b = toLex (Sum.inl i') := by rw [← hi']; rfl
          rw [h1, h2, hab]
        · obtain ⟨a, ha, hfa⟩ := hIf m hm
          exact ⟨a, ha, hfa⟩
      have hcard : Pᶜ.card = L.card := by
        have hu : (uni I L).card = I.card + L.card := by simp [uni]
        rw [Finset.card_compl, Fintype.card_fin, hPcard]
        omega
      have hu := Units.mul_inv (T.Y j)
      have hsplit : ∀ (c1 c2 : Prop) [Decidable c1] [Decidable c2] (x y1 y2 : S),
          ((if c1 then x * y1 else 0) - if c2 then x * y2 else 0) =
            x * ((if c1 then y1 else 0) - if c2 then y2 else 0) := by
        intros
        split_ifs <;> ring
      obtain ⟨s, hs, hdet⟩ := det_form (T.R I J) (Matrix.of fun a b => T.rowMu (e a) b) P I f
        (fun m => (T.X m : S)) (T.Y j : S)
        (fun a m => Sum.elim (fun _ => (0 : S)) (fun l => ((if m = (ofLex l).1 then (T.Y (ofLex l).2 : S) else 0) -
          if m = (ofLex l).2 then (T.Y (ofLex l).1 : S) else 0) * (((T.Y j)⁻¹ : Sˣ) : S)) (ofLex (e a)))
        (by
          intro a ha m
          obtain ⟨i, hi⟩ := (hPm a).1 ha
          simp only [Matrix.of_apply, Sys.rowMu, hi, Sum.elim_inl, Pi.single_apply, hf a i hi])
        hfI hIf
        (by
          intro a ha m hm
          rcases hx : ofLex (e a) with i | l
          · exact absurd ((hPm a).2 ⟨i, hx⟩) ha
          · simp only [Matrix.of_apply, Sys.rowMu, hx, Sum.elim_inr]
            rw [hsplit]
            linear_combination (-((T.X m : S) * ((if m = (ofLex l).1 then (T.Y (ofLex l).2 : S) else 0) -
              if m = (ofLex l).2 then (T.Y (ofLex l).1 : S) else 0))) * hu)
        (by
          intro a m
          rcases hx : ofLex (e a) with i | l
          · simp only [hx, Sum.elim_inl]
            exact zero_mem _
          · simp only [hx, Sum.elim_inr, sub_mul, ite_mul, zero_mul]
            rw [← Units.val_mul, ← Units.val_mul]
            refine sub_mem ?_ ?_
            · split_ifs
              · exact hT.memY I J hI j hj _
              · exact zero_mem _
            · split_ifs
              · exact hT.memY I J hI j hj _
              · exact zero_mem _)
      beta_reduce at hdet
      refine ⟨s, hs, ?_⟩
      rw [hdet, hcard]
    · rw [dite_eq_right h]
      exact ⟨0, zero_mem _, by ring⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PoincareLelong
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma inter_inr_card {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ] (_i : DecidableEq (β ⊕ₗ κ))
    (b : Finset β) (L : Finset κ) :
    (uni b L ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding).card = L.card := by
  have h : uni b L ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding =
      L.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding := by
    ext t
    obtain ⟨t, rfl⟩ := toLex.surjective t
    rcases t with i | l <;> simp [uni, inrE]
  rw [h, Finset.card_map]

private lemma inl_not_mem {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ] (i : β) :
    (inlE i : β ⊕ₗ κ) ∉ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding := by
  simp [inlE, inrE]

private lemma inr_mem {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ] (l : κ) :
    (inrE l : β ⊕ₗ κ) ∈ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding := by
  simp

theorem UpperTheory.Gal.productCup_of_system.localOne_of_gl1 :
    FiltrationBoundaryCriterion → ColQEx → WdUni → L1 := by
  intro hG hC hU β κ E _ _ _ _ _ _ A w d n hW hK c hc hd hB
  have e : ∀ s : Finset (β ⊕ₗ κ), uni (lft s) (rgt s) = s := (hU β κ E w c ∅ ∅).2.2.2.2
  have eL : ∀ (b : Finset β) (L : Finset κ), lft (uni b L) = b := fun b L => (hU β κ E w c b L).2.1
  have eR : ∀ (b : Finset β) (L : Finset κ), rgt (uni b L) = L := fun b L => (hU β κ E w c b L).2.2.1
  have eC : ∀ s : Finset (β ⊕ₗ κ), s.card = (lft s).card + (rgt s).card := fun s => by
    have := (hU β κ E w c (lft s) (rgt s)).2.2.2.1
    rwa [e s] at this
  have hS : ∀ (_i : DecidableEq (β ⊕ₗ κ)) (s : Finset (β ⊕ₗ κ)),
      (s ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding).card = (rgt s).card := fun i s => by
    have := inter_inr_card i (lft s) (rgt s)
    rwa [e s] at this
  have hy : ∀ b : Finset β, (b.card : ℤ) = n - d →
      ∃ y ∈ (colA A w b).C (d - 1), (colA A w b).D y = col c b := fun b hb => by
    obtain ⟨y, hy, h⟩ := hB b hb
    exact ⟨y, hy, h⟩
  let yb : Finset β → Finset κ → E := fun b => if h : (b.card : ℤ) = n - d then (hy b h).choose else 0
  have hyb : ∀ b, (b.card : ℤ) = n - d → yb b ∈ (colA A w b).C (d - 1) ∧ (colA A w b).D (yb b) = col c b := by
    intro b hb
    simp only [yb, dif_pos hb]
    exact (hy b hb).choose_spec
  have hy0 : ∀ b, ¬ (b.card : ℤ) = n - d → yb b = 0 := by
    intro b hb
    simp only [yb, dif_neg hb]
  let y : Finset (β ⊕ₗ κ) → E := fun s => ((-1 : ℤ) ^ (lft s).card) • yb (lft s) (rgt s)
  have hmem : ∀ b, (b.card : ℤ) = n - d → ∀ L, yb b L ∈ (if (L.card : ℤ) = d - 1 then A (uni b L) else ⊥) := by
    intro b hb L
    have h : yb b ∈ Submodule.pi Set.univ
      (fun L : Finset κ => if (L.card : ℤ) = d - 1 then A (uni b L) else ⊥) := (hyb b hb).1
    exact (Submodule.mem_pi.1 h) L (Set.mem_univ _)
  have hz : ∀ s, ¬ (((lft s).card : ℤ) = n - d ∧ ((rgt s).card : ℤ) = d - 1) → y s = 0 := by
    intro s hs
    by_cases hb : ((lft s).card : ℤ) = n - d
    · have hL : ¬ ((rgt s).card : ℤ) = d - 1 := fun h => hs ⟨hb, h⟩
      have h1 := hmem _ hb (rgt s)
      rw [if_neg hL, Submodule.mem_bot] at h1
      simp only [y, h1, smul_zero]
    · simp only [y, hy0 _ hb, Pi.zero_apply, smul_zero]
  have hcC : ∀ s : Finset (β ⊕ₗ κ), ¬ (s.card : ℤ) = n → c s = 0 := by
    intro s hs
    have h : c ∈ Submodule.pi Set.univ
      (fun s : Finset (β ⊕ₗ κ) => if (s.card : ℤ) = n then A s else ⊥) := hc.1
    have h1 := (Submodule.mem_pi.1 h) s (Set.mem_univ _)
    rwa [if_neg hs, Submodule.mem_bot] at h1
  refine hG (β ⊕ₗ κ) E A w (Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding) d n hW
    (hC β κ E A w d hK) c hc ?_ ⟨y, ?_, ?_, ?_⟩
  · intro s hs
    have hs' : d < ((rgt s).card : ℤ) := by
      rw [hS _ s] at hs
      exact not_le.1 hs
    have := hd (lft s) (rgt s) hs'
    rwa [e s] at this
  · refine Submodule.mem_pi.2 fun s _ => ?_
    by_cases h : ((lft s).card : ℤ) = n - d ∧ ((rgt s).card : ℤ) = d - 1
    · have hcard : (s.card : ℤ) = n - 1 := by
        rw [eC s]; push_cast; omega
      have h1 := hmem _ h.1 (rgt s)
      rw [if_pos h.2, e s] at h1
      show y s ∈ (if (s.card : ℤ) = n - 1 then A s else ⊥)
      rw [if_pos hcard]
      exact zsmul_mem h1 _
    · rw [hz s h]
      exact zero_mem _
  · intro s hs
    rw [hS _ s] at hs
    exact hz s fun h => hs h.2
  · intro s hs
    rw [hS _ s] at hs
    conv_lhs => rw [← e s]
    rw [(hU β κ E _ y (lft s) (rgt s)).1]
    have h0 : ∀ _i : DecidableEq (β ⊕ₗ κ),
        (fun i : β => wOn (Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding) w (inlE i)) = fun _ => 0 := by
      intro _i
      funext i
      simp only [wOn, if_neg (inl_not_mem i)]
    have h1 : ∀ _i : DecidableEq (β ⊕ₗ κ),
        (fun l : κ => wOn (Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding) w (inrE l)) = fun l => w (inrE l) := by
      intro _i
      funext l
      simp only [wOn, if_pos (inr_mem l)]
    have h2 : (fun L' : Finset κ => y (uni (lft s) L')) = ((-1 : ℤ) ^ (lft s).card) • yb (lft s) := by
      funext L'
      simp only [y, eL, eR, Pi.smul_apply]
    have h3 : wd (fun _ : β => (0 : Module.End ℂ E)) (fun b' => y (uni b' (rgt s))) (lft s) = 0 := by
      simp [wd]
    rw [h0 _, h1 _, h3, zero_add, h2, map_zsmul, Pi.smul_apply, smul_smul, ← mul_pow]
    by_cases hb : ((lft s).card : ℤ) = n - d
    · have h4 := congrFun (hyb _ hb).2 (rgt s)
      have h5 : wd (fun l : κ => w (inrE l)) (yb (lft s)) (rgt s) = c s := by
        have : col c (lft s) (rgt s) = c s := by
          show c (uni (lft s) (rgt s)) = c s
          rw [e s]
        rw [← this]
        exact h4
      rw [h5]
      simp
    · rw [hy0 _ hb, hcC s (by rw [eC s]; push_cast; omega)]
      simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.RowMuNull
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)

private lemma card_uni {β κ : Type} [LinearOrder β] [LinearOrder κ] (I : Finset β) (J : Finset κ) :
    (uni I J).card = I.card + J.card := by
  simp [uni]

private lemma mem_uni {β κ : Type} [LinearOrder β] [LinearOrder κ] (I : Finset β) (J : Finset κ)
    (t : β ⊕ₗ κ) : t ∈ uni I J ↔ (∃ i ∈ I, t = toLex (Sum.inl i)) ∨ ∃ l ∈ J, t = toLex (Sum.inr l) := by
  simp only [uni, Finset.mem_map, Finset.mem_disjSum, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨a, (⟨i, hi, rfl⟩ | ⟨l, hl, rfl⟩), rfl⟩
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨l, hl, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact ⟨Sum.inl i, Or.inl ⟨i, hi, rfl⟩, rfl⟩
    · exact ⟨Sum.inr l, Or.inr ⟨l, hl, rfl⟩, rfl⟩

private lemma detC_eq {κ : Type} [LinearOrder κ] {p : ℕ} (ρ : κ → Fin p → S) (s : Finset κ)
    (f : Fin p → κ) (hc : s.card = p) (hs : ∀ x, f x ∈ s) (hf : StrictMono f) :
    detC ρ s = (Matrix.of fun a b => ρ (f a) b).det := by
  unfold detC
  rw [dite_eq_left hc, Finset.orderEmbOfFin_unique hc hs hf]

private lemma rowMu_inr (l : Mi d) (m : Fin (d + 1)) : T.rowMu (toLex (Sum.inr l)) m =
    (if m = (ofLex l).1 then (T.X m * T.Y (ofLex l).2 : S) else 0) -
      if m = (ofLex l).2 then (T.X m * T.Y (ofLex l).1 : S) else 0 := rfl

private lemma rowMu_inl (i m : Fin (d + 1)) : T.rowMu (toLex (Sum.inl i)) m =
    (Pi.single i 1 : Fin (d + 1) → S) m := rfl

private lemma rowMu_sum (t : Fin (d + 1) ⊕ₗ Mi d) :
    ∑ b, T.rowMu t b * (1 : Fin (d + 1) → S) b = app (fun _ => (1 : S)) T.mu t := by
  obtain ⟨t, rfl⟩ := toLex.surjective t
  rcases t with i | l
  · simp [rowMu_inl, app]
  · simp only [rowMu_inr, Pi.one_apply, mul_one, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rfl

private lemma rowMu_null (l : Mi d) :
    ∑ m, T.rowMu (toLex (Sum.inr l)) m * ((T.Y m * (T.X m)⁻¹ : Sˣ) : S) = 0 := by
  simp only [rowMu_inr, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Units.val_mul]
  have h1 : ((T.X (ofLex l).1 : Sˣ) : S) * (((T.X (ofLex l).1)⁻¹ : Sˣ) : S) = 1 := Units.mul_inv _
  have h2 : ((T.X (ofLex l).2 : Sˣ) : S) * (((T.X (ofLex l).2)⁻¹ : Sˣ) : S) = 1 := Units.mul_inv _
  linear_combination ((T.Y (ofLex l).1 : S) * (T.Y (ofLex l).2 : S)) * (h1 - h2)

private lemma detC_left (L : Finset (Mi d)) : detC T.rowMu (uni ∅ L) = 0 := by
  unfold detC
  split_ifs with h
  · set A : Matrix (Fin (d + 1)) (Fin (d + 1)) S :=
      Matrix.of fun a b => T.rowMu ((uni ∅ L).orderEmbOfFin h a) b with hA
    have hAv : A.mulVec (fun m => ((T.Y m * (T.X m)⁻¹ : Sˣ) : S)) = 0 := by
      funext a
      have hmem : (uni ∅ L).orderEmbOfFin h a ∈ uni ∅ L := Finset.orderEmbOfFin_mem _ _ _
      rw [mem_uni] at hmem
      rcases hmem with ⟨i, hi, _⟩ | ⟨l, _, hl⟩
      · simp at hi
      · simp only [Matrix.mulVec, dotProduct, hA, Matrix.of_apply, hl, Pi.zero_apply]
        exact rowMu_null T l
    have h0 := congrArg A.adjugate.mulVec hAv
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_zero, Matrix.smul_mulVec,
      Matrix.one_mulVec] at h0
    have h1 := congrFun h0 0
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    exact (Units.mul_left_eq_zero (T.Y 0 * (T.X 0)⁻¹)).1 h1
  · rfl

private lemma detC_univ : detC T.rowMu (uni Finset.univ ∅) = 1 := by
  rw [detC_eq T.rowMu _ (fun a => toLex (Sum.inl a)) (by simp [card_uni])
    (fun x => (mem_uni _ _ _).2 (Or.inl ⟨x, Finset.mem_univ _, rfl⟩))
    (fun a b h => Sum.Lex.inl_strictMono h)]
  have : (Matrix.of fun a b => T.rowMu (toLex (Sum.inl a)) b) = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) S) := by
    ext a b
    simp [rowMu_inl, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this, Matrix.det_one]

private lemma detC_top : detC T.rowMu (uni {0} (img (dj 0))) =
    (∏ l : Fin d, (T.X l.succ : S)) * (T.Y 0 : S) ^ d := by
  let f : Fin (d + 1) → Fin (d + 1) ⊕ₗ Mi d :=
    Fin.cons (toLex (Sum.inl 0)) fun l => toLex (Sum.inr (dj 0 l))
  have hf0 : f 0 = toLex (Sum.inl 0) := rfl
  have hfs : ∀ l : Fin d, f l.succ = toLex (Sum.inr (dj 0 l)) := fun _ => rfl
  have hmono : StrictMono f := by
    intro a b h
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact absurd h (lt_irrefl _)
      | succ b => rw [hf0, hfs]; exact Sum.Lex.inl_lt_inr _ _
    | succ a =>
      induction b using Fin.cases with
      | zero => exact absurd h (Fin.not_lt_zero _)
      | succ b =>
        rw [hfs, hfs]
        exact Sum.Lex.inr_strictMono ((dj 0).strictMono (Fin.succ_lt_succ_iff.1 h))
  have hmem : ∀ x, f x ∈ uni {0} (img (dj 0)) := by
    intro x
    induction x using Fin.cases with
    | zero => exact (mem_uni _ _ _).2 (Or.inl ⟨0, by simp, rfl⟩)
    | succ l => exact (mem_uni _ _ _).2 (Or.inr ⟨dj 0 l, by simp [img], rfl⟩)
  rw [detC_eq T.rowMu _ f (by simp [card_uni, img, add_comm]) hmem hmono]
  have hrow : ∀ (l : Fin d) (m : Fin (d + 1)), T.rowMu (f l.succ) m =
      (if m = l.succ then (T.X m * T.Y 0 : S) else 0) -
        if m = 0 then (T.X m * T.Y l.succ : S) else 0 := by
    intro l m
    have e1 : (ofLex (dj (0 : Fin (d + 1)) l)).1 = l.succ := by simp [dj]
    have e2 : (ofLex (dj (0 : Fin (d + 1)) l)).2 = 0 := rfl
    rw [hfs, rowMu_inr, e1, e2]
  rw [Matrix.det_of_lowerTriangular]
  · rw [Fin.prod_univ_succ]
    simp only [Matrix.of_apply, hf0, rowMu_inl, Pi.single_eq_same, one_mul, hrow]
    simp [Finset.prod_mul_distrib, Fin.succ_ne_zero]
  · intro i j hij
    have hij' : i < j := hij
    simp only [Matrix.of_apply]
    induction i using Fin.cases with
    | zero =>
      rw [hf0, rowMu_inl]
      simp [Pi.single_apply, (Fin.pos_iff_ne_zero.1 hij')]
    | succ l =>
      rw [hrow]
      have h1 : j ≠ l.succ := ne_of_gt hij'
      have h2 : j ≠ 0 := by
        rintro rfl
        exact Fin.not_lt_zero _ hij'
      simp [h1, h2]

end

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.thMu_of :
    Det → ThMu := by
  intro hDet d S E _ _ _ _ T
  refine ⟨?_, detC_left T, detC_univ T, detC_top T⟩
  have h := hDet S S (Algebra.lmul ℂ S) (Fin (d + 1) ⊕ₗ Mi d) (d + 1) T.rowMu 1 1
  simp only [rowMu_sum] at h
  have e : (fun s => (Algebra.lmul ℂ S) (detC T.rowMu s) (1 : S)) = detC T.rowMu := by
    funext s
    simp
  rwa [e] at h
end

