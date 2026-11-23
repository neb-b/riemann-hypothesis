module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Bundle0005
public import Lemmata.GeneralBFactRight.Imports
public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.CapelliZ
section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

def CapScalar : Prop :=
  ∀ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
    ∀ s ∈ nablaSq ℂ n mu, ∀ u : ℂ,
      Formalism.REAL.qdet (capE h lam) u (φ s) = (∏ k : Fin n, (u - (k : ℂ) + (mu.w k : ℂ))) • φ s

def capF {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (i : Fin n) (v : ℤ) :
    Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
  ((-1 : ℂ) ^ n) • Formalism.REAL.qdet (capE h lam) (-((v : ℂ) - ((i.1 : ℤ) : ℂ)))

def capZ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
  ((List.finRange n).map fun i =>
    ((((Rset h lam sg i).erase (sg.w i)).toList.map fun v => capF h lam i v).prod)).prod

theorem list_scalar {V ι : Type*} [AddCommGroup V] [Module ℂ V] (L : List ι) (F : ι → Module.End ℂ V)
    (c : ι → ℂ) (x : V) (hL : ∀ j ∈ L, F j x = c j • x) : (L.map F).prod x = (L.map c).prod • x := by
  first | exact Bl.general_b_fact_right.goal1 .. | (apply Bl.general_b_fact_right.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right.goal1 <;> assumption) | (apply @Bl.general_b_fact_right.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right.goal1 <;> assumption) | (apply @Bl.general_b_fact_right.goal1 <;> first | assumption | infer_instance)

theorem capF_scalar (hC : CapScalar) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu) (i : Fin n) (v : ℤ) :
    capF h lam i v (φ s) = (∏ j : Fin n, ((((v - (i.1 : ℤ)) - mu.w j + (j.1 : ℤ) : ℤ)) : ℂ)) • φ s := by
  rw [capF, LinearMap.smul_apply, hC h lam mu φ hφ s hs, smul_smul]
  congr 1
  have : ((-1 : ℂ) ^ n) = ∏ _j : Fin n, (-1 : ℂ) := by simp
  rw [this, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  push_cast; ring

theorem capZ_scalar (hC : CapScalar) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu) :
    capZ h lam sg (φ s) = ((zScalar h lam sg mu : ℤ) : ℂ) • φ s := by
  unfold capZ
  rw [list_scalar (List.finRange n) _
    (fun i => ∏ v ∈ (Rset h lam sg i).erase (sg.w i),
      ∏ j : Fin n, ((((v - (i.1 : ℤ)) - mu.w j + (j.1 : ℤ) : ℤ)) : ℂ)) (φ s)]
  · rw [← Fin.prod_univ_def]
    unfold zScalar
    push_cast
    rfl
  · intro i _
    rw [list_scalar _ _ (fun v => ∏ j : Fin n, ((((v - (i.1 : ℤ)) - mu.w j + (j.1 : ℤ) : ℤ)) : ℂ)) (φ s),
      Finset.prod_map_toList]
    intro v _
    exact capF_scalar hC h lam mu φ hφ s hs i v

def presRing {N : ℕ} (lam : DomWeight N) : Subring (Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ)) where
  carrier := {Q | ∀ f ∈ nablaSq ℤ N lam, ∃ f' ∈ nablaSq ℤ N lam,
    Q (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) f'}
  mul_mem' := by
    intro Q1 Q2 h1 h2 f hf
    obtain ⟨f2, hf2, e2⟩ := h2 f hf
    obtain ⟨f3, hf3, e3⟩ := h1 f2 hf2
    exact ⟨f3, hf3, by rw [Module.End.mul_apply, e2, e3]⟩
  one_mem' := fun f hf => ⟨f, hf, rfl⟩
  add_mem' := by
    intro Q1 Q2 h1 h2 f hf
    obtain ⟨f1, hf1, e1⟩ := h1 f hf
    obtain ⟨f2, hf2, e2⟩ := h2 f hf
    exact ⟨f1 + f2, add_mem hf1 hf2, by rw [LinearMap.add_apply, e1, e2, map_add (f := _)]⟩
  zero_mem' := fun f hf => ⟨0, zero_mem _, by simp⟩
  neg_mem' := by
    intro Q h1 f hf
    obtain ⟨f1, hf1, e1⟩ := h1 f hf
    exact ⟨-f1, neg_mem hf1, by rw [LinearMap.neg_apply, e1, map_neg]⟩

theorem algebraMap_int_mem {N : ℕ} (lam : DomWeight N) (w : ℤ) :
    algebraMap ℂ (Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ)) (w : ℂ) ∈ presRing lam := by
  rw [map_intCast]; exact intCast_mem _ w

theorem pol_mem_presRing {N : ℕ} (lam : DomWeight N) (a b : Fin N) :
    (pol ℂ (m := N) a b : Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ)) ∈ presRing lam := by
  intro f hf
  exact ⟨pol ℤ a b f, pol_mem_dualWeyl ℤ lam.natW a b f hf, pol_map _ a b f⟩

theorem capE_mem {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (a b : Fin n) : capE h lam a b ∈ presRing lam := by
  unfold capE
  refine add_mem (pol_mem_presRing lam _ _) ?_
  split_ifs
  · exact algebraMap_int_mem lam _
  · exact zero_mem _

theorem qdet_mem {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (w : ℤ) :
    Formalism.REAL.qdet (capE h lam) (w : ℂ) ∈ presRing lam := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine Subring.sum_mem _ fun σ _ => mul_mem (intCast_mem _ _) (Subring.list_prod_mem _ fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  unfold Formalism.REAL.Tm
  refine add_mem ?_ (capE_mem h lam _ _)
  split_ifs
  · have : (w : ℂ) - (k : ℂ) = ((w - (k.1 : ℤ) : ℤ) : ℂ) := by push_cast; rfl
    rw [this]; exact algebraMap_int_mem lam _
  · exact zero_mem _

theorem capF_mem {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (i : Fin n) (v : ℤ) :
    capF h lam i v ∈ presRing lam := by
  unfold capF
  have h1 : (-((v : ℂ) - ((i.1 : ℤ) : ℂ))) = ((-(v - (i.1 : ℤ)) : ℤ) : ℂ) := by push_cast; ring
  have h2 : ((-1 : ℂ) ^ n) = (((-1 : ℤ) ^ n : ℤ) : ℂ) := by push_cast; ring
  rw [h1, h2, Algebra.smul_def]
  exact mul_mem (algebraMap_int_mem lam _) (qdet_mem h lam _)

theorem capZ_mem {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    capZ h lam sg ∈ presRing lam := by
  unfold capZ
  refine Subring.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  refine Subring.list_prod_mem _ fun y hy => ?_
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
  exact capF_mem h lam i v

theorem capelliZ_of (hC : CapScalar) : CapelliZ := by
  intro n N h lam sg _
  refine ⟨capZ h lam sg, fun f hf => capZ_mem h lam sg f hf, ?_⟩
  intro mu _ φ hφ s hs
  exact capZ_scalar hC h lam sg mu φ hφ s hs

end PI.WGL
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleF
section
noncomputable section

namespace PI.WGL.LTF

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD PI.WGL.LTE

theorem gmin_rowW {r c m : ℕ} (ρ : Fin m → Fin r) (κ : Fin m → Fin c) :
    IsWeightedHomogeneous (rowW r c) (gmin ρ κ) (∑ p, (Pi.single (ρ p) 1 : Fin r → ℕ)) := by
  classical
  unfold gmin
  rw [Matrix.det_apply, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun σ _ => ?_
  refine Submodule.smul_of_tower_mem _ _ ?_
  rw [mem_weightedHomogeneousSubmodule]
  have hp := IsWeightedHomogeneous.prod Finset.univ
    (fun p => (X (ρ (σ p), κ p) : MvPolynomial (Fin r × Fin c) ℤ))
    (fun p => rowW r c (ρ (σ p), κ p)) (fun p _ => isWeightedHomogeneous_X ℤ _ _)
  have hsum : ∑ p, rowW r c (ρ (σ p), κ p) = ∑ p, (Pi.single (ρ p) 1 : Fin r → ℕ) := by
    simp only [rowW]
    exact Equiv.sum_comp σ (fun p => (Pi.single (ρ p) 1 : Fin r → ℕ))
  rw [hsum] at hp
  simpa [Matrix.of_apply] using hp

theorem bidet_rowW {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin n) :
    IsWeightedHomogeneous (rowW n n) (bideterminant ℤ sz hsz I) (tupCnt I) := by
  unfold bideterminant
  have hp := IsWeightedHomogeneous.prod Finset.univ (fun k => initMinor ℤ (n := n) (I k) (hsz k))
    (fun k => ∑ p, (Pi.single (I k p) 1 : Fin n → ℕ)) (fun k _ => gmin_rowW (I k) (Fin.castLE (hsz k)))
  convert hp using 1
  ext a
  unfold tupCnt
  simp only [Finset.sum_apply, Finset.card_filter, Pi.single_apply, eq_comm]

def w0r {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : Fin N → ℕ :=
  ∑ i : Fin n, ((if i.1 + 1 = n then (aa h lam sg i).toNat else 0) • initW N (i.1 + 1) +
    (if i.1 = 0 then (bb h lam sg i).toNat else 0) • (∑ p, (Pi.single (rowsZ h i p) 1 : Fin N → ℕ)))

theorem ite_pow_rowW {N : ℕ} (c : Prop) [Decidable c] (f : MvPolynomial (Fin N × Fin N) ℤ) (w : Fin N → ℕ)
    (hf : IsWeightedHomogeneous (rowW N N) f w) (e : ℕ) :
    IsWeightedHomogeneous (rowW N N) (if c then f ^ e else 1) ((if c then e else 0) • w) := by
  split_ifs
  · exact hf.pow e
  · simpa using isWeightedHomogeneous_one ℤ (rowW N N)

theorem constant_weighted_homogeneous {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    IsWeightedHomogeneous (rowW N N) (C0 h lam sg) (w0r h lam sg) := by
  have hlp : ∀ (s : ℕ) (hr : s ≤ N) (hc : s ≤ N),
      IsWeightedHomogeneous (rowW N N) (lpMinor ℤ s hr hc) (initW N s) := by
    intro s hr hc
    have hg : IsWeightedHomogeneous (rowW N N) (lpMinor ℤ s hr hc)
        (∑ p, (Pi.single (Fin.castLE hr p) 1 : Fin N → ℕ)) := gmin_rowW (Fin.castLE hr) (Fin.castLE hc)
    have hw : (∑ p, (Pi.single (Fin.castLE hr p) 1 : Fin N → ℕ)) = initW N s := by
      funext t
      simp only [Finset.sum_apply, Pi.single_apply, initW, Fin.ext_iff, Fin.coe_castLE]
      rw [show (∑ p : Fin s, if (t : ℕ) = (p : ℕ) then 1 else 0) = ∑ p : Fin s, if (p : ℕ) = t.1 then 1 else 0 from
        Finset.sum_congr rfl (fun p _ => by simp only [eq_comm])]
      rw [sum_ite_val (fun _ => 1) t.1]
      simp
    rw [hw] at hg
    exact hg
  unfold C0 w0r
  refine IsWeightedHomogeneous.prod Finset.univ _ _ fun i _ => ?_
  refine IsWeightedHomogeneous.mul ?_ ?_
  · exact ite_pow_rowW _ _ _ (hlp _ _ _) _
  · exact ite_pow_rowW _ _ _ (gmin_rowW (rowsZ h i) (Fin.castLE _)) _

def wk {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (lifted : Prop) [Decidable lifted] : Fin N → ℕ :=
  (∑ q, (Pi.single (eRow h (ρ q)) 1 : Fin N → ℕ)) +
    (if lifted then (Pi.single (⟨N - 1, by omega⟩ : Fin N) 1 : Fin N → ℕ) else 0)

theorem G_rowW {n N : ℕ} (h : n + 1 = N) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K))
    (k : Fin K) (ρ : Fin (sz k) → Fin n) :
    IsWeightedHomogeneous (rowW N N)
      (if k ∈ L then lif h ρ (by have := hsz k; omega) else unl h ρ (by have := hsz k; omega))
      (wk h ρ (k ∈ L)) := by
  unfold wk
  split_ifs with hk
  · unfold lif
    have hg : IsWeightedHomogeneous (rowW N N)
        (initMinor ℤ (liftRows h ρ) (by have := hsz k; omega : sz k + 1 ≤ N))
        (∑ p, (Pi.single (liftRows h ρ p) 1 : Fin N → ℕ)) :=
      gmin_rowW (liftRows h ρ) (Fin.castLE (by have := hsz k; omega : sz k + 1 ≤ N))
    have hw : (∑ p, (Pi.single (liftRows h ρ p) 1 : Fin N → ℕ)) =
        (∑ q, (Pi.single (eRow h (ρ q)) 1 : Fin N → ℕ)) + Pi.single (⟨N - 1, by omega⟩ : Fin N) 1 := by
      rw [Fin.sum_univ_castSucc]
      simp [liftRows]
    rw [hw] at hg
    exact hg
  · unfold unl
    have hg : IsWeightedHomogeneous (rowW N N)
        (initMinor ℤ (eRow h ∘ ρ) (by have := hsz k; omega : sz k ≤ N))
        (∑ p, (Pi.single (eRow h (ρ p)) 1 : Fin N → ℕ)) :=
      gmin_rowW (eRow h ∘ ρ) (Fin.castLE (by have := hsz k; omega : sz k ≤ N))
    rw [add_zero]
    exact hg

theorem constant_weight_apply {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (av : ℕ) (hav : av < N) :
    w0r h lam sg ⟨av, hav⟩ =
      (if hn : n - 1 < n then (aa h lam sg ⟨n - 1, hn⟩).toNat * (if av < n then 1 else 0) else 0) +
      (if hn : 0 < n then (bb h lam sg ⟨0, hn⟩).toNat * (if av = n then 1 else 0) else 0) := by
  unfold w0r
  have key : ∀ i : Fin n, (((if i.1 + 1 = n then (aa h lam sg i).toNat else 0) • initW N (i.1 + 1) +
      (if i.1 = 0 then (bb h lam sg i).toNat else 0) • (∑ p, (Pi.single (rowsZ h i p) 1 : Fin N → ℕ)))
        ⟨av, hav⟩) =
      (if i.1 = n - 1 then (aa h lam sg i).toNat * (if av < n then 1 else 0) else 0) +
      (if i.1 = 0 then (bb h lam sg i).toNat * (if av = n then 1 else 0) else 0) := by
    intro i
    have hi2 := i.2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    · by_cases hi : i.1 + 1 = n
      · rw [if_pos hi, if_pos (by omega)]
        simp only [initW, hi]
      · rw [if_neg hi, if_neg (by omega), zero_mul]
    · by_cases hi : i.1 = 0
      · rw [if_pos hi, if_pos hi]
        congr 1
        rw [Finset.sum_apply]
        have e : ∀ p : Fin (i.1 + 1), (Pi.single (rowsZ h i p) 1 : Fin N → ℕ) ⟨av, hav⟩ =
            if av = n then 1 else 0 := by
          intro p
          have hp := p.2
          have hr : rowsZ h i p = ⟨N - 1, by omega⟩ := by
            simp only [rowsZ]
            rw [if_pos (by omega)]
          rw [hr, Pi.single_apply]
          by_cases hav' : av = n
          · rw [if_pos (Fin.ext (by simp only; omega)), if_pos hav']
          · rw [if_neg (fun he => hav' (by have := congrArg Fin.val he; simp only at this; omega)), if_neg hav']
        rw [Finset.sum_congr rfl (fun p _ => e p), Finset.sum_const, Finset.card_univ, Fintype.card_fin, hi,
          smul_eq_mul, zero_add, one_mul]
      · rw [if_neg hi, if_neg hi, zero_mul]
  rw [Finset.sum_apply, Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, sum_ite_val,
    sum_ite_val]

theorem cardL {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (hshape : shapeDeg sz = sg.natW) (L : Finset (Fin K)) (hL : GoodL h lam sg sz L) :
    L.card = ∑ i : Fin n, (if i.1 = 0 then 0 else (bb h lam sg i).toNat) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := sz) (t := Finset.range n) ?_]
  · rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hL.2 i]
    congr 1
    ext k
    simp [Finset.mem_filter]
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_range]
    replace hk := Finset.mem_coe.mp hk
    rcases sz_lt sg sz hsz hshape k with h1 | h1
    · exact h1
    · exact absurd h1 (Nat.pos_iff_ne_zero.mp (hL.1 k hk))

theorem sumB {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg) :
    ((∑ i : Fin n, (bb h lam sg i).toNat : ℕ) : ℤ) = degZ lam sg - lam.detShift := by
  subst h
  have hb : ∀ i : Fin n, (((bb rfl lam sg i).toNat : ℕ) : ℤ) = lam.w (Fin.castSucc i) - sg.w i :=
    fun i => b_val rfl lam sg hI i.1 i.2
  push_cast
  rw [Finset.sum_congr rfl (fun i _ => hb i), Finset.sum_sub_distrib]
  unfold degZ wsum
  rw [Fin.sum_univ_castSucc (f := lam.w), lam_detShift rfl lam,
    show (Fin.last n) = (⟨n, by omega⟩ : Fin (n + 1)) from rfl]
  ring

end PI.WGL.LTF
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.SqActMemNabla
section
noncomputable section

namespace PI.WGL.Adj

open Formalism.BasicNotions MvPolynomial

def gStar {N : ℕ} (g : GL (Fin N) ℂ) : GL (Fin N) ℂ where
  val := Matrix.conjTranspose (g : Matrix (Fin N) (Fin N) ℂ)
  inv := Matrix.conjTranspose ((g⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
  val_inv := by rw [← Matrix.conjTranspose_mul]; simp
  inv_val := by rw [← Matrix.conjTranspose_mul]; simp

theorem gStar_val {N : ℕ} (g : GL (Fin N) ℂ) :
    ((gStar g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = Matrix.conjTranspose (g : Matrix (Fin N) (Fin N) ℂ) := rfl

theorem gStar_gStar {N : ℕ} (g : GL (Fin N) ℂ) : gStar (gStar g) = g := by
  ext i j; simp [gStar_val]

def cU (a : ℂˣ) : ℂˣ := Units.map (starRingEnd ℂ : ℂ →* ℂ) a

theorem cU_zpow_val (a : ℂˣ) (e : ℤ) : ((cU a ^ e : ℂˣ) : ℂ) = star ((a ^ e : ℂˣ) : ℂ) := by
  unfold cU
  rw [← map_zpow, Units.coe_map]
  rfl

theorem embGL_gStar {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) :
    embGL ℂ n N h (gStar g) = gStar (embGL ℂ n N h g) := by
  have key : ∀ p q : Fin n ⊕ Fin 1,
      Matrix.fromBlocks (Matrix.conjTranspose (g : Matrix (Fin n) (Fin n) ℂ)) 0 0 1 p q =
        (starRingEnd ℂ) (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 1 q p) := by
    rintro (p | p) (q | q)
    · simp [Matrix.conjTranspose_apply]
    · simp
    · simp
    · have hp : p = q := Subsingleton.elim _ _
      subst hp; simp
  ext i j
  simp only [embGL, blkHom, gStar_val, Matrix.conjTranspose_apply]
  simp
  exact key _ _

theorem lastGL_cU (N : ℕ) (a : ℂˣ) : lastGL ℂ N (cU a) = gStar (lastGL ℂ N a) := by
  ext i j
  simp only [lastGL, diagGL, gStar_val, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; split_ifs <;> simp [cU]
  · have hji : j ≠ i := fun e => hij e.symm
    simp [hij, hji]

theorem detPow_gStar {N : ℕ} (g : GL (Fin N) ℂ) (k : ℤ) :
    detPow ℂ N (gStar g) k = star (detPow ℂ N g k) := by
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, star_zpow₀]
  congr 1
  simp [gStar_val, Matrix.det_conjTranspose]

theorem sqAct_mem_nabla {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ nablaSq ℂ N lam) : sqAct ℂ N lam g f ∈ nablaSq ℂ N lam := by
  unfold sqAct
  exact Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N lam.natW _ f hf)

theorem sqAct_smul {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (c : ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqAct ℂ N lam g (c • f) = c • sqAct ℂ N lam g f := by
  unfold sqAct
  rw [map_smul, smul_comm]

theorem nf_sqAct_adj {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (sqAct ℂ N lam g x) y = normFock lam x (sqAct ℂ N lam (gStar g) y) := by
  have hm : Matrix.conjTranspose (Matrix.transpose (g : Matrix (Fin N) (Fin N) ℂ)) =
      Matrix.transpose ((gStar g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
    ext i j; simp [gStar_val, Matrix.conjTranspose_apply]
  have hf : Formalism.REAL.fockF (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.transpose (g : Matrix (Fin N) (Fin N) ℂ)) x) y =
      Formalism.REAL.fockF x (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
        (Matrix.transpose ((gStar g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) y) := by
    rw [Formalism.GradedWeylDivisibility.fockRowAdj, hm]
  unfold sqAct
  rw [nf_smul_left, nf_smul_right, detPow_gStar, star_star]
  unfold normFock
  rw [hf]

theorem nf_sqAct_adj' {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam x (sqAct ℂ N lam g y) = normFock lam (sqAct ℂ N lam (gStar g) x) y := by
  rw [nf_sqAct_adj, gStar_gStar]

theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (by have := lam.anti hij; linarith)

theorem extremal_mem {N : ℕ} (lam : DomWeight N) : extremal ℂ N lam ∈ nablaSq ℂ N lam :=
  Formalism.GradedWeylDivisibility.hwMem ℂ N N le_rfl lam.natW (natW_anti lam)

theorem extremal_ne {N : ℕ} (lam : DomWeight N) : extremal ℂ N lam ≠ 0 :=
  Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl lam.natW

end PI.WGL.Adj
end
end

