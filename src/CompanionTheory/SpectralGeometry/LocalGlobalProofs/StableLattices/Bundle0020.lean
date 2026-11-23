module

public import Mathlib
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Formalism.RealPlaceAnalysis.Bundle0004
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0012

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SumInsertErase
section
open Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DSChainAdj

open CompanionTheory.D.DSIC

variable {n : ℕ} {ε : Fin n → Bool}

theorem sg_insert (i : NC ε) (A : Finset (NC ε)) : sg i (insert i A) = sg i A := by
  unfold sg
  rw [Finset.filter_insert, if_neg (lt_irrefl _)]

theorem conj_sg (i : NC ε) (A : Finset (NC ε)) : (starRingEnd ℂ) (sg i A) = sg i A := by
  unfold sg
  simp

theorem sum_insert_erase (i : NC ε) (f : Finset (NC ε) → Finset (NC ε) → ℂ) :
    (∑ A : Finset (NC ε), if i ∈ A then 0 else f (insert i A) A) =
      ∑ B : Finset (NC ε), if i ∈ B then f B (B.erase i) else 0 := by
  have h1 : (∑ A : Finset (NC ε), if i ∈ A then 0 else f (insert i A) A) =
      ∑ A ∈ univ.filter (fun A : Finset (NC ε) => i ∉ A), f (insert i A) A := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun A _ => ?_
    by_cases h : i ∈ A <;> simp [h]
  rw [h1, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun A => insert i A) (fun B => B.erase i) ?_ ?_ ?_ ?_ ?_
  · intro A _
    simp
  · intro B _
    simp
  · intro A hA
    have hA' : i ∉ A := by simpa using hA
    exact Finset.erase_insert hA'
  · intro B hB
    have hB' : i ∈ B := by simpa using hB
    exact Finset.insert_erase hB'
  · intro A hA
    have hA' : i ∉ A := by simpa using hA
    simp only [Finset.erase_insert hA']

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem term_adj (i : NC ε) (T T' : Module.End ℂ V) (h : ∀ x y : V, ⟪T x, y⟫_ℂ = -⟪x, T' y⟫_ℂ) (w x : Ch ε V) :
    ip (lift ε T (ann i w)) x = -ip w (lift ε T' (cre i x)) := by
  unfold ip
  have key := sum_insert_erase i (fun B A => sg i B * ⟪T (w B), x A⟫_ℂ)
  have hL : (∑ A, ⟪lift ε T (ann i w) A, x A⟫_ℂ) =
      ∑ A : Finset (NC ε), if i ∈ A then 0 else sg i (insert i A) * ⟪T (w (insert i A)), x A⟫_ℂ := by
    refine Finset.sum_congr rfl fun A _ => ?_
    by_cases hA : i ∈ A
    · simp [ann, hA]
    · simp [ann, hA, conj_sg, sg_insert, mul_comm]
  have hR : -(∑ A, ⟪w A, lift ε T' (cre i x) A⟫_ℂ) =
      ∑ B : Finset (NC ε), if i ∈ B then sg i B * ⟪T (w B), x (B.erase i)⟫_ℂ else 0 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun A _ => ?_
    by_cases hA : i ∈ A
    · simp [cre, hA, h]
    · simp [cre, hA]
  rw [hL, hR, key]

theorem ip_sum_left {ι : Type} (s : Finset ι) (f : ι → Ch ε V) (x : Ch ε V) :
    ip (∑ i ∈ s, f i) x = ∑ i ∈ s, ip (f i) x := by
  unfold ip
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_apply, sum_inner]

theorem ip_sum_right {ι : Type} (s : Finset ι) (f : ι → Ch ε V) (w : Ch ε V) :
    ip w (∑ i ∈ s, f i) = ∑ i ∈ s, ip w (f i) := by
  unfold ip
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_apply, inner_sum]

theorem adj : CompanionTheory.D.DSIC.Adj := by
  intro n ε V _ _ E hE w x
  unfold bd bdA cob
  rw [LinearMap.sum_apply, LinearMap.sum_apply, ip_sum_left, ip_sum_right, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  refine term_adj i _ _ (fun a b => ?_) w x
  have h := hE i.1.1 i.1.2 a b
  have h1 := i.2.1
  have h2 := i.2.2
  rw [h]
  simp [Formalism.REAL.sgn, h1, h2]

end GlobalTheory.CompanionTheory.DSChainAdj
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TransferStatementBis
section
open CompanionTheory.Rg.Fl
open CompanionTheory.D.gk.admitted (stdPoly word word_nil word_cons)

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeTransfer

section Words

variable {R : Type*} [Ring R]

theorem word_one (l : List R) : word (1 : R) l = l.prod := by
  induction l with
  | nil => rw [word_nil, List.prod_nil]
  | cons a l ih => rw [word_cons, ih, List.prod_cons, one_mul]

theorem word_mul_idem {E : R} (hE : E * E = E) (l : List R) : word E l * E = word E l := by
  induction l with
  | nil => rw [word_nil, hE]
  | cons a l ih => rw [word_cons, mul_assoc, ih]

theorem sum_reverse_eq_zero {M : ℕ} (b : Fin M → R) (h : stdPoly (1 : R) b = 0) :
    ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).reverse.prod = 0 := by
  have h' : ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).prod = 0 := by
    rw [← h]
    unfold CompanionTheory.D.gk.admitted.stdPoly
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [word_one, zsmul_eq_mul]
  have hrev : ∀ f : Fin M → R, (List.ofFn f).reverse = List.ofFn fun i => f i.rev := by
    intro f
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
      congr 1
      ext
      simp only [Fin.val_rev]
      simp only [List.length_reverse, List.length_ofFn] at h1
      omega
  have hsq : (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) *
      (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  calc ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).reverse.prod
      = ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) •
          ((Equiv.Perm.sign (π * Fin.revPerm) : ℤ) •
            (List.ofFn fun i => b ((π * Fin.revPerm : Equiv.Perm (Fin M)) i)).prod) := by
        refine Finset.sum_congr rfl fun π _ => ?_
        rw [hrev, smul_smul, Equiv.Perm.sign_mul, Units.val_mul, mul_comm (Equiv.Perm.sign π : ℤ),
          ← mul_assoc, hsq, one_mul]
        all_goals rfl
    _ = (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) •
          ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign (π * Fin.revPerm) : ℤ) •
            (List.ofFn fun i => b ((π * Fin.revPerm : Equiv.Perm (Fin M)) i)).prod := by
        rw [Finset.smul_sum]
    _ = (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin M)) : ℤ) •
          ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).prod := by
        congr 1
        exact Equiv.sum_comp (Equiv.mulRight Fin.revPerm)
          (fun π : Equiv.Perm (Fin M) => (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).prod)
    _ = 0 := by rw [h', smul_zero]

end Words

variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def phi (K : Subgroup G) (σ : G →* (H →L[ℂ] H)) (v : H) : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] H :=
  Finsupp.linearCombination ℂ fun x : G ⧸ K => σ (Quotient.out x) v

abbrev dlt (K : Subgroup G) : (G ⧸ K) →₀ ℂ := Finsupp.single ((1 : G) : G ⧸ K) 1

variable {K : Subgroup G} {σ : G →* (H →L[ℂ] H)} {v : H}

theorem phi_single (hv : ∀ k ∈ K, σ k v = v) (x : G) (c : ℂ) :
    phi K σ v (Finsupp.single (x : G ⧸ K) c) = c • σ x v := by
  rw [phi, Finsupp.linearCombination_single]
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
  rw [hk, map_mul, ContinuousLinearMap.mul_apply, hv k k.2]

theorem lam_single (g x : G) (c : ℂ) :
    lam K g (Finsupp.single (x : G ⧸ K) c) = Finsupp.single ((g * x : G) : G ⧸ K) c := by
  simp only [CompanionTheory.Rg.Fl.lam, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    MulAction.Quotient.smul_mk, smul_eq_mul]

theorem phi_lam (hv : ∀ k ∈ K, σ k v = v) (g : G) (f : (G ⧸ K) →₀ ℂ) :
    phi K σ v (lam K g f) = σ g (phi K σ v f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f₁ f₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]
  | single y c =>
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [lam_single, phi_single hv, phi_single hv, map_mul, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.map_smul]

theorem lam_dlt {k : G} (hk : k ∈ K) : lam K k (dlt K) = dlt K := by
  simp only [dlt]
  rw [lam_single, mul_one]
  congr 1
  exact QuotientGroup.eq.2 (by simpa using K.inv_mem hk)

theorem hk_comm (h : Hk K) (g : G) (f : (G ⧸ K) →₀ ℂ) :
    lam K g ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) f) = (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (lam K g f) := by
  have hc := (Subalgebra.mem_centralizer_iff ℂ).1 h.2 (lam K g) ⟨g, rfl⟩
  exact congrArg (fun T : Module.End ℂ ((G ⧸ K) →₀ ℂ) => T f) hc

theorem phi_fixed (hv : ∀ k ∈ K, σ k v = v) (h : Hk K) :
    ∀ k ∈ K, σ k (phi K σ v ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K))) =
      phi K σ v ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)) := by
  intro k hk
  rw [← phi_lam hv, hk_comm, lam_dlt hk]

theorem phi_phi (hv : ∀ k ∈ K, σ k v = v) (h : Hk K) (f : (G ⧸ K) →₀ ℂ) :
    phi K σ (phi K σ v ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K))) f =
      phi K σ v ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f₁ f₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]
  | single y c =>
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hd : lam K x (dlt K) = Finsupp.single (x : G ⧸ K) 1 := by
      simp only [dlt]
      rw [lam_single, mul_one]
    rw [phi_single (phi_fixed hv h), ← phi_lam hv, hk_comm, hd,
      ← Finsupp.smul_single_one (x : G ⧸ K) c, LinearMap.map_smul, LinearMap.map_smul]

theorem avg_sigma {E : H →L[ℂ] H} (hA : IsAvg σ K E) (hv : ∀ k ∈ K, σ k v = v) (g : G) (T : Hk K)
    (S : Finset (G ⧸ K)) (hS : (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K))
    (hT : (T : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K) = ∑ y ∈ S, Finsupp.single y (1 : ℂ)) :
    E (σ g v) = phi K σ v ((((S.card : ℂ)⁻¹ • T : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)) := by
  have hcard : (S.card : ℂ) ≠ 0 := by
    have hmem : (g : G ⧸ K) ∈ S := by
      have : (g : G ⧸ K) ∈ (↑S : Set (G ⧸ K)) := by
        rw [hS]
        exact MulAction.mem_orbit_self _
      exact Finset.mem_coe.1 this
    exact Nat.cast_ne_zero.2 (Finset.card_pos.2 ⟨_, hmem⟩).ne'
  have hterm : ∀ y ∈ S, E (phi K σ v (Finsupp.single y 1)) = E (σ g v) := by
    intro y hy
    have hy' : y ∈ MulAction.orbit K (g : G ⧸ K) := by
      rw [← hS]
      exact hy
    obtain ⟨k, rfl⟩ := hy'
    show E (phi K σ v (Finsupp.single (((k : G) * g : G) : G ⧸ K) 1)) = E (σ g v)
    rw [phi_single hv, one_smul, map_mul,
      ContinuousLinearMap.mul_apply, hA.2.2 _ _ k.2]
  have hfix := phi_fixed hv (((S.card : ℂ)⁻¹ • T : Hk K))
  rw [← hA.2.1 _ hfix, Subalgebra.coe_smul, LinearMap.smul_apply, hT]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sum]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

theorem word_apply {E : H →L[ℂ] H} (hA : IsAvg σ K E) (b : G → Hk K)
    (hb : ∀ (u : H), (∀ k ∈ K, σ k u = u) → ∀ g, E (σ g u) = phi K σ u ((b g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)))
    (hv : ∀ k ∈ K, σ k v = v) (l : List G) :
    word E (l.map fun g => σ g) v =
      phi K σ v ((((l.map b).reverse.prod : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)) := by
  induction l with
  | nil =>
    simp only [List.map_nil, word_nil, List.reverse_nil, List.prod_nil, OneMemClass.coe_one,
      Module.End.one_apply, dlt, phi_single hv, one_smul, map_one, ContinuousLinearMap.one_apply]
    exact hA.2.1 v hv
  | cons g l ih =>
    simp only [List.map_cons, word_cons, ContinuousLinearMap.mul_apply]
    rw [ih, hb _ (phi_fixed hv _) g, phi_phi hv]
    simp only [List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
      MulMemClass.coe_mul, Module.End.mul_apply]

theorem stTransfer : StTransfer := by
  intro G _ K M hK hPI H _ _ _ σ _ E hA g
  obtain ⟨T, hT, -, -⟩ := GlobalTheory.T.hecke_operators_span_and_faithful G K hK
  have hfin : ∀ x : G, (MulAction.orbit K (x : G ⧸ K)).Finite := hK
  let S : G → Finset (G ⧸ K) := fun x => (hfin x).toFinset
  have hS : ∀ x, (↑(S x) : Set (G ⧸ K)) = MulAction.orbit K (x : G ⧸ K) :=
    fun x => (hfin x).coe_toFinset
  let b : G → Hk K := fun x => (((S x).card : ℂ)⁻¹ • T x : Hk K)
  have hb : ∀ u : H, (∀ k ∈ K, σ k u = u) → ∀ x, E (σ x u) =
      phi K σ u ((b x : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)) :=
    fun u hu x => avg_sigma hA hu x (T x) (S x) (hS x) (hT x (S x) (hS x))
  have hEE : E * E = E := by
    ext v
    exact hA.2.1 (E v) (hA.1 v)
  have hpoly : stdPoly E (fun i => σ (g i)) * E = stdPoly E (fun i => σ (g i)) := by
    unfold CompanionTheory.D.gk.admitted.stdPoly
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [mul_assoc, word_mul_idem hEE]
  have key : ∀ u : H, (∀ k ∈ K, σ k u = u) → (stdPoly E fun i => σ (g i)) u = 0 := by
    intro u hu
    let A : (H →L[ℂ] H) →+ H :=
      { toFun := fun W => W u, map_zero' := rfl, map_add' := fun _ _ => rfl }
    let L : Hk K →+ H :=
      { toFun := fun h => phi K σ u ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)),
        map_zero' := by simp,
        map_add' := fun x y => by simp [map_add (f := _)] }
    have hw : ∀ π : Equiv.Perm (Fin M), A (word E (List.ofFn fun i => σ (g (π i)))) =
        L (List.ofFn fun i => b (g (π i))).reverse.prod := by
      intro π
      have := word_apply hA b hb hu (List.ofFn fun i => g (π i))
      rw [List.map_ofFn, List.map_ofFn] at this
      exact this
    have h0 := sum_reverse_eq_zero (fun i => b (g i)) (hPI _)
    show A (stdPoly E fun i => σ (g i)) = 0
    unfold CompanionTheory.D.gk.admitted.stdPoly
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    calc ∑ π : Equiv.Perm (Fin M), A (↑↑(Equiv.Perm.sign π) * word E (List.ofFn fun i => σ (g (π i))))
        = ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • L (List.ofFn fun i => b (g (π i))).reverse.prod := by
          refine Finset.sum_congr rfl fun π _ => ?_
          rw [← zsmul_eq_mul, map_zsmul, hw]
      _ = L (∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (g (π i))).reverse.prod) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          simp only [map_zsmul]
      _ = 0 := by rw [h0, map_zero]
  ext v
  rw [ContinuousLinearMap.zero_apply, ← hpoly, ContinuousLinearMap.mul_apply]
  exact key _ (hA.1 v)

end GlobalTheory.CompanionTheory.HeckeTransfer
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WlemOfGfacts
section
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.DSICWLem

open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)

def ht {n : ℕ} (w : Fin n → ℝ) : ℝ := ∑ c : Fin n, ((n : ℝ) - (c : ℕ)) * w c

theorem ht_add_root {n : ℕ} (w : Fin n → ℝ) (c d : Fin n) (h : c < d) :
    ht w < ht (w + Pi.single c 1 - Pi.single d 1) := by
  have hcd : ((c : ℕ) : ℝ) < ((d : ℕ) : ℝ) := by exact_mod_cast h
  have : ht (w + Pi.single c 1 - Pi.single d 1) =
      ht w + ((n : ℝ) - (c : ℕ)) - ((n : ℝ) - (d : ℕ)) := by
    simp [ht, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply]
  rw [this]
  linarith

theorem wlem_of_gfacts (hG : GFacts) : WLem := by
  intro n ε V _ _ E γ x hx hK
  obtain ⟨g, hg, -, hwt, hdiag, -⟩ := hG n ε
  classical
  have hne : (univ.filter fun A : Finset (NC ε) => x A ≠ 0).Nonempty := by
    by_contra hc
    apply hx
    funext A
    by_contra hA
    exact hc ⟨A, by simpa using hA⟩
  obtain ⟨A, hA, hmin⟩ := Finset.exists_min_image _ (fun A : Finset (NC ε) => ht (wtA A)) hne
  have hA0 : x A ≠ 0 := by simpa using hA
  refine ⟨A, hA0, ?_⟩
  have hF : ∀ c d, Fop ε E c d x A = E c d (x A) + ∑ B, (g c d A B : ℂ) • x B := by
    intro c d
    rw [← hg V c d x A]
    rfl
  refine ⟨fun a => ?_, fun a b hab hε => ?_⟩
  · have h1 := congrFun (hK.1 a) A
    rw [hF] at h1
    have h2 : ∑ B, (g a a A B : ℂ) • x B = (wtA A a : ℂ) • x A := by
      rw [Finset.sum_eq_single A]
      · simp [hdiag]
      · intro B _ hB
        simp [hdiag, Ne.symm hB]
      · simp
    rw [h2, Pi.smul_apply] at h1
    rw [Pi.sub_apply, Complex.ofReal_sub, sub_smul, ← h1, add_sub_cancel_right]
  · have h1 := congrFun (hK.2 a b hab hε) A
    rw [hF] at h1
    have h2 : ∑ B, (g a b A B : ℂ) • x B = 0 := by
      refine Finset.sum_eq_zero fun B _ => ?_
      by_cases hgB : g a b A B = 0
      · simp [hgB]
      by_cases hxB : x B = 0
      · simp [hxB]
      exfalso
      have h3 := hmin B (by simpa using hxB)
      have h4 := ht_add_root (wtA B) a b hab
      rw [← (hwt a b A B hgB).2] at h4
      exact absurd h3 (not_le.mpr h4)
    rw [h2, add_zero] at h1
    exact h1

end GlobalTheory.CompanionTheory.DSICWLem
end
end

