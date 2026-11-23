module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
public import Mathlib.Topology.Algebra.ClopenNhdofOne

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Descend
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem gen {Γ Γb M R κ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group Γb]
    [TopologicalSpace Γb] [Monoid M] [CommRing R] (I : Ideal R) [IsHausdorff I R] (N : Set Γ) (π : Γ →* Γb)
    (hq : Topology.IsQuotientMap π) (hk : π.ker = (Subgroup.normalClosure N).topologicalClosure)
    (e : κ → M → R) (he : ∀ x y, (∀ k, e k x = e k y) → x = y) (r : Γ →* M) (hN : ∀ g ∈ N, r g = 1)
    (hc : ∀ k, AdicCont I fun g => e k (r g)) :
    ∃ rb : Γb →* M, rb.comp π = r ∧ ∀ k, AdicCont I fun g => e k (rb g) := by
  have hcl : IsClosed (r.ker : Set Γ) := by
    have : (r.ker : Set Γ) = ⋂ k, ⋂ n : ℕ,
        {g | Ideal.Quotient.mk (I ^ n) (e k (r g)) = Ideal.Quotient.mk (I ^ n) (e k 1)} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      refine ⟨fun h k n => by rw [h], fun h => he _ _ fun k => ?_⟩
      rw [← sub_eq_zero]
      refine IsHausdorff.haus (I := I) inferInstance _ fun n => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
      exact h k n
    rw [this]
    exact isClosed_iInter fun k => isClosed_iInter fun n => (hc k n).isClosed_fiber _
  have hle : π.ker ≤ r.ker := by
    rw [hk]
    exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => hN g hg) hcl
  have hle' : π.ker ≤ r.toHomUnits.ker := fun g hg => Units.ext (hle hg)
  have hs := hq.surjective
  let φ := π.liftOfRightInverse (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨r.toHomUnits, hle'⟩
  have hφ : ∀ g, ((Units.coeHom M).comp φ) (π g) = r g := fun g =>
    congrArg Units.val (π.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hs) ⟨r.toHomUnits, hle'⟩ g)
  refine ⟨(Units.coeHom M).comp φ, MonoidHom.ext hφ, fun k n s => ?_⟩
  rw [← hq.isOpen_preimage]
  have := hc k n s
  simp only [← hφ] at this
  exact this

theorem UpperTheory.V.Ws.X1.descend :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (Φ : Fr O Γ) , ∀ {Γb : Type} [Group Γb] [TopologicalSpace Γb] [IsTopologicalGroup Γb] [T2Space Γb] (π : Γ →* Γb), Φ.Quo π → ∀ {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R], (∀ (r : Γ →* M4 R), (∀ g ∈ Φ.N, r g = 1) → (∀ i j, AdicCont I fun g => r g i j) → ∃ rb : Γb →* M4 R, rb.comp π = r ∧ ∀ i j, AdicCont I fun g => rb g i j) ∧ ∀ (ν : Γ →* Rˣ), (∀ g ∈ Φ.N, ν g = 1) → AdicCont I (fun g => (ν g : R)) → ∃ νb : Γb →* Rˣ, νb.comp π = ν ∧ AdicCont I fun g => (νb g : R) := by
  intro O Γ _ _ _ _ _ Φ Γb _ _ _ _ π hπ R _ I _
  have hq : Topology.IsQuotientMap π := hπ.cont.isClosedMap.isQuotientMap hπ.cont hπ.onto
  refine ⟨fun r hN hc => ?_, fun ν hN hc => ?_⟩
  · obtain ⟨rb, h1, h2⟩ := gen I Φ.N π hq hπ.ker (fun (k : Fin 4 × Fin 4) (x : M4 R) => x k.1 k.2)
      (fun x y h => Matrix.ext fun i j => h (i, j)) r hN fun k => hc k.1 k.2
    exact ⟨rb, h1, fun i j => h2 (i, j)⟩
  · obtain ⟨rb, h1, h2⟩ := gen I Φ.N π hq hπ.ker (fun (_ : Unit) (x : Rˣ) => (x : R))
      (fun x y h => Units.ext (h ())) ν hN fun _ => hc
    exact ⟨rb, h1, h2 ()⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.DiagLift
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.X1.exists_symplectic_diagonalizing_lift {A R : Type} [CommRing A] [CommRing R] (f : A →+* R)
    (hsq : ∀ a b, f a = 0 → f b = 0 → a * b = 0) (ν : A) (X : M4 A) (hν : IsUnit ν) (hX : IsGSp ν X)
    (hd : ∀ i j, i ≠ j → f (X i j) = 0) (hu : ∀ i j, i ≠ j → IsUnit (X i i - X j j)) :
    ∃ u : M4 A, IsGSp 1 u ∧ u.map f = 1 ∧ (adj u * X * u).IsDiag := by
  obtain ⟨hmul, -, hadd, -, hone, hmap, -⟩ := grp A
  have mz : ∀ M M' : M4 A, M.map f = 0 → M'.map f = 0 → M * M' = 0 := by
    intro M M' h h'
    ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => hsq _ _ (congrFun (congrFun h i) k) (congrFun (congrFun h' k) j)
  set D : M4 A := Matrix.diagonal fun i => X i i with hD
  set E : M4 A := X - D with hE
  have hXE : X = D + E := by rw [hE]; abel
  have Eii : ∀ i, E i i = 0 := fun i => by simp [hE, hD]
  have Eij : ∀ i j, i ≠ j → E i j = X i j := fun i j h => by simp [hE, hD, Matrix.diagonal_apply_ne _ h]
  have Ef : E.map f = 0 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Eii]
    · simp [Eij i j h, hd i j h]
  have aEf : (adj E).map f = 0 := by
    rw [← hmap, Ef]; ext i j; simp [adj_apply]
  have aD : adj D = Matrix.diagonal fun i => X i.rev i.rev := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, hD, Matrix.diagonal_apply]
  have key : adj D * D + (adj D * E + adj E * D) = ν • (1 : M4 A) := by
    have h : adj (D + E) * (D + E) = ν • (1 : M4 A) := by rw [← hXE]; exact hX
    rw [hadd, add_mul, mul_add, mul_add, mz _ _ aEf Ef] at h
    rw [← h]; abel
  have k1 : ∀ i, X i.rev i.rev * X i i = ν := fun i => by
    have h := congrFun (congrFun key i) i
    rw [aD, hD] at h
    simpa [Matrix.diagonal_mul_diagonal, adj_apply, Eii] using h
  have k2 : ∀ i j, i ≠ j → X i.rev i.rev * E i j + adj E i j * X j j = 0 := fun i j hij => by
    have h := congrFun (congrFun key i) j
    rw [aD, hD] at h
    simpa [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij] using h
  set N : M4 A := Matrix.of fun i j => -(E i j * Ring.inverse (X i i - X j j)) with hN
  have Nf : N.map f = 0 := by
    ext i j
    have h : f (E i j) = 0 := congrFun (congrFun Ef i) j
    simp [hN, h]
  have N1 : ∀ i j, i ≠ j → N i j * (X i i - X j j) = -E i j := fun i j h => by
    rw [hN, Matrix.of_apply, neg_mul, mul_assoc, Ring.inverse_mul_cancel _ (hu i j h), mul_one]
  have aN : adj N = -N := by
    ext i j
    by_cases h : i = j
    · subst h; simp [adj_apply, hN, Eii]
    · have h' : j.rev ≠ i.rev := fun e => h (Fin.rev_injective e).symm
      have uj : IsUnit (X j j) := isUnit_of_mul_isUnit_right (by rw [k1 j]; exact hν)
      have e1 := N1 i j h
      have e2 : adj N i j * (X j.rev j.rev - X i.rev i.rev) = -adj E i j := by
        rw [adj_apply, adj_apply, smul_mul_assoc, N1 _ _ h', smul_neg]
      refine ((hu _ _ h').mul uj).mul_left_inj.mp ?_
      rw [Matrix.neg_apply]
      linear_combination X j j * e2 - k2 i j h + X i.rev i.rev * e1 + N i j * k1 j - N i j * k1 i
  have au : adj (1 + N) = 1 - N := by rw [hadd, hone, aN, sub_eq_add_neg]
  refine ⟨1 + N, ?_, ?_, ?_⟩
  · unfold IsGSp
    rw [au, one_smul, sub_mul, mul_add N, mz _ _ Nf Nf]
    simp
  · rw [Matrix.map_add _ (map_add f), Nf, add_zero, Matrix.map_one _ (map_zero f) (map_one f)]
  · have NDf : (N * D).map f = 0 := by rw [Matrix.map_mul, Nf, zero_mul]
    have e : adj (1 + N) * X * (1 + N) = D + (E + D * N - N * D) := by
      have : (1 - N) * (D + E) * (1 + N) = D + (E + D * N - N * D) + (E * N - N * D * N - N * E - N * E * N) := by
        noncomm_ring
      rw [au]
      conv_lhs => rw [hXE]
      rw [this, mz _ _ Ef Nf, mz _ _ NDf Nf, mz _ _ Nf Ef]
      simp
    intro i j h
    rw [e, hD]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.diagonal_apply_ne _ h]
    linear_combination N1 i j h

theorem UpperTheory.V.Ws.X1.diagLift :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (ν : A) (X : M4 A), IsUnit ν → IsGSp ν X → (X.map p).IsDiag → (∀ i j, i ≠ j → IsUnit (X i i - X j j)) → ∃ u : M4 A, IsGSp 1 u ∧ u.map p = 1 ∧ (adj u * X * u).IsDiag := by
  intro Λ _ _ _ _ A R _ _ _ _ _ _ p _ hk ν X hν hX hd hu
  have hle : RingHom.ker p ≤ maximalIdeal A := le_maximalIdeal (RingHom.ker_ne_top p)
  refine UpperTheory.V.Ws.X1.exists_symplectic_diagonalizing_lift (p : A →+* R) (fun a b ha hb => ?_) ν X hν hX (fun i j h => hd h) hu
  have h : a * b ∈ maximalIdeal A * RingHom.ker p := Ideal.mul_mem_mul (hle ha) hb
  rwa [hk] at h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.DualZero
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1

private theorem tri_zero {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (ht : Fin 4 → ℤ)
    (hinj : Function.Injective ht) (hb : ∀ i j, ht i - ht j < 4) (hr : ∀ g i j, ht i < ht j → r g i j = 0)
    (ω : Γ → k) (hω : ∀ i j, ∃ g, r g i i * r g⁻¹ j j ≠ ω g) (F : M4 k →ₗ[k] k)
    (hF : ∀ g Y, F (r g * Y * r g⁻¹) = ω g * F Y) : F = 0 := by
  have hexp : ∀ Y : M4 k, F Y = ∑ a, ∑ b, Y a b * F (Matrix.single a b 1) := by
    intro Y
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [show Matrix.single a b (Y a b) = Y a b • Matrix.single a b (1 : k) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  have hent : ∀ (A B : M4 k) (i j a b : Fin 4), (A * (Matrix.single i j 1 : M4 k) * B : M4 k) a b = A a i * B j b := by
    intro A B i j a b
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_mul]
  have main : ∀ n : ℕ, ∀ i j, 4 - (n : ℤ) ≤ ht i - ht j → F (Matrix.single i j 1) = 0 := by
    intro n
    induction n with
    | zero =>
      intro i j hij
      exfalso
      have := hb i j
      push_cast at hij
      omega
    | succ n ih =>
      intro i j hij
      by_cases hlt : 4 - (n : ℤ) ≤ ht i - ht j
      · exact ih i j hlt
      obtain ⟨g, hg⟩ := hω i j
      have hsum := hF g (Matrix.single i j 1)
      rw [hexp (r g * Matrix.single i j 1 * r g⁻¹)] at hsum
      simp only [hent] at hsum
      have inner : ∑ b, r g i i * r g⁻¹ j b * F (Matrix.single i b 1)
          = r g i i * r g⁻¹ j j * F (Matrix.single i j 1) := by
        refine Finset.sum_eq_single j (fun b _ hbj => ?_) (fun h => absurd (Finset.mem_univ _) h)
        by_cases hjb : ht j < ht b
        · rw [hr g⁻¹ j b hjb]
          ring
        · have hne : ht b ≠ ht j := fun e => hbj (hinj e)
          rw [ih i b (by push_cast at hij hlt ⊢; omega)]
          ring
      have outer : ∑ a, ∑ b, r g a i * r g⁻¹ j b * F (Matrix.single a b 1)
          = ∑ b, r g i i * r g⁻¹ j b * F (Matrix.single i b 1) := by
        refine Finset.sum_eq_single i (fun a _ hai => ?_) (fun h => absurd (Finset.mem_univ _) h)
        apply Finset.sum_eq_zero
        intro b _
        by_cases hia : ht a < ht i
        · rw [hr g a i hia]
          ring
        by_cases hjb : ht j < ht b
        · rw [hr g⁻¹ j b hjb]
          ring
        have hne : ht a ≠ ht i := fun e => hai (hinj e)
        rw [ih a b (by push_cast at hij hlt ⊢; omega)]
        ring
      rw [outer, inner] at hsum
      have e : (r g i i * r g⁻¹ j j - ω g) * F (Matrix.single i j 1) = 0 := by
        rw [sub_mul, hsum, sub_self]
      exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hg)
  apply LinearMap.ext
  intro Y
  rw [hexp Y, LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  rw [main 8 a b (by have := hb b a; push_cast; omega), mul_zero]

private theorem adj_conj {Γ k : Type} [Group Γ] [CommRing k] {r : Γ →* M4 k} (h : ∀ g, ∃ ν, IsGSp ν (r g)) (g : Γ)
    (X : M4 k) : adj (r g * X * r g⁻¹) = r g * adj X * r g⁻¹ := by
  obtain ⟨ν, hν⟩ := h g
  obtain ⟨μ, hμ⟩ := h g⁻¹
  have G := grp k
  have e1 : r g * r g⁻¹ = 1 := by rw [← r.map_mul, mul_inv_cancel, r.map_one]
  have e2 : r g⁻¹ * r g = 1 := by rw [← r.map_mul, inv_mul_cancel, r.map_one]
  have a1 : adj (r g) = ν • r g⁻¹ := G.2.2.2.2.2.2.1 ν _ _ hν e1
  have a2 : adj (r g⁻¹) = μ • r g := G.2.2.2.2.2.2.1 μ _ _ hμ e2
  have hprod := G.2.2.2.2.2.2.2.1 ν μ _ _ hν hμ
  rw [e1] at hprod
  have e : adj (1 : M4 k) * 1 = (ν * μ) • (1 : M4 k) := hprod
  rw [G.2.2.2.2.1, Matrix.mul_one] at e
  have e00 := congrFun (congrFun e 0) 0
  simp at e00
  have hμν : μ * ν = 1 := by rw [mul_comm]; exact e00.symm
  rw [G.1, G.1, a1, a2, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, hμν, one_smul, Matrix.mul_assoc]

private theorem rt_wt {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ)
    (hm : ∀ i g, Φ.χ i g * Φ.χ i.rev g = Φ.ν g) (i j : Fin 4) (g : Γ) :
    Φ.rt (wt i j) g = Φ.χ i g * Φ.χ j g⁻¹ := by
  have hd : Φ.χ 3 g = Φ.ν g * (Φ.χ 0 g)⁻¹ := eq_mul_inv_of_mul_eq (by rw [mul_comm]; exact hm 0 g)
  have hc : Φ.χ 2 g = Φ.ν g * (Φ.χ 1 g)⁻¹ := eq_mul_inv_of_mul_eq (by rw [mul_comm]; exact hm 1 g)
  rw [map_inv]
  fin_cases i <;> fin_cases j <;> simp [Fr.rt, wt, lamW, muW, hc, hd] <;>
    (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]; abel)

end UpperTheory.V.Ws.X1

theorem UpperTheory.V.Ws.X1.dualZero :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k), Φ.Ok a → ∀ (c : PD Φ.ι Γ k), Φ.Res a c → ∀ (h : ∀ g, ∃ x, IsGSp x (c.r g)) (ω : Γ → k), (∀ w, ∃ g, a (Φ.rt w g) ≠ ω g) → ∀ f : sp4 k →ₗ[k] k, (∀ g X, f (adSp c.r h g X) = ω g * f X) → f = 0 := by
  intro O Γ _ _ _ Φ k _ a hok c hres h ω hωw f hf
  have G := grp k
  have adj_add := G.2.2.1
  have adj_smul := G.2.2.2.1
  have adj_adj := G.2.1
  let AdjL : M4 k →ₗ[k] M4 k := { toFun := adj, map_add' := adj_add, map_smul' := adj_smul }
  have h2 : (2 : k) ≠ 0 := hok.two.ne_zero
  set t : k := (2 : k)⁻¹ with htdef
  have hsub : ∀ Y : M4 k, adj (Y - adj Y) = adj Y - Y := by
    intro Y
    have e := map_sub AdjL Y (adj Y)
    simp only [AdjL, LinearMap.coe_mk, AddHom.coe_mk] at e
    rw [e, adj_adj]
  let π : M4 k →ₗ[k] sp4 k := LinearMap.codRestrict (sp4 k) (t • (LinearMap.id - AdjL)) (fun Y => by
    show adj (t • (Y - adj Y)) = -(t • (Y - adj Y))
    rw [adj_smul, hsub, ← smul_neg, neg_sub])
  have hπ : ∀ Y, ((π Y : sp4 k) : M4 k) = t • (Y - adj Y) := fun Y => rfl
  let F : M4 k →ₗ[k] k := f ∘ₗ π
  have hFc : ∀ g Y, F (c.r g * Y * c.r g⁻¹) = ω g * F Y := by
    intro g Y
    have e : π (c.r g * Y * c.r g⁻¹) = adSp c.r h g (π Y) := by
      apply Subtype.ext
      rw [adSp_val, hπ, hπ, adj_conj h g Y]
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
    show f (π _) = ω g * f (π Y)
    rw [e, hf]
  have hfix : ∀ X : sp4 k, π X = X := by
    intro X
    apply Subtype.ext
    rw [hπ]
    have hX : adj (X : M4 k) = -(X : M4 k) := X.2
    rw [hX, sub_neg_eq_add, ← two_smul k (X : M4 k), smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hω' : ∀ i j, ∃ g, c.r g i i * c.r g⁻¹ j j ≠ ω g := by
    intro i j
    obtain ⟨g, hg⟩ := hωw (wt i j)
    refine ⟨g, ?_⟩
    rw [hres.diag, hres.diag]
    rw [rt_wt Φ hok.mul i j g, Units.val_mul, map_mul] at hg
    exact hg
  have key : ∀ ht : Fin 4 → ℤ, Function.Injective ht → (∀ i j, ht i - ht j < 4) →
      (∀ g i j, ht i < ht j → c.r g i j = 0) → f = 0 := by
    intro ht hi hb hr
    have hF0 := tri_zero c.r ht hi hb hr ω hω' F hFc
    apply LinearMap.ext
    intro X
    have e : F X = 0 := by rw [hF0]; rfl
    calc f X = f (π X) := by rw [hfix X]
      _ = F X := rfl
      _ = 0 := e
  rcases hres.shape with ⟨hS, _⟩ | hS
  · refine key ![-3, -1, -2, 0] (by decide) (by decide) ?_
    intro g i j hlt
    apply hS g i j
    · fin_cases i <;> fin_cases j <;> simp at hlt ⊢
    · fin_cases i <;> fin_cases j <;> simp [nP, wt, lamW, muW, wAl, wBe, wPs, wTh] at hlt ⊢
  · refine key ![-3, -2, -1, 0] (by decide) (by decide) ?_
    intro g i j hlt
    apply hS g i j
    · fin_cases i <;> fin_cases j <;> simp at hlt ⊢
    · fin_cases i <;> fin_cases j <;> simp [nM, wt, lamW, muW, wAl, wBe, wPs, wTh] at hlt ⊢
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.GenOfMax
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem gen_of_max {A : Type} [CommGroup A] (l : ℕ)
    (hl : ∀ s t : A, s ^ l = 1 → t ^ l = 1 → s ≠ 1 → ∃ n : ℕ, t = s ^ n)
    (a : ℕ) (z : A) (h1 : z ^ l ^ (a + 1) = 1) (h0 : z ^ l ^ a ≠ 1) :
    ∀ b, b ≤ a + 1 → ∀ s : A, s ^ l ^ b = 1 → s ∈ Subgroup.zpowers z := by
  intro b
  induction b with
  | zero => intro _ s hs; simp at hs; simp [hs]
  | succ b ih =>
    intro hb s hs
    obtain ⟨n, hn⟩ := hl (z ^ l ^ a) (s ^ l ^ b) (by rw [← pow_mul, ← pow_succ, h1])
      (by rw [← pow_mul, ← pow_succ, hs]) h0
    obtain ⟨c, rfl⟩ : ∃ c, a = c + b := ⟨a - b, by omega⟩
    have h2 : (s / z ^ (l ^ c * n)) ^ l ^ b = 1 := by
      rw [div_pow, hn, ← pow_mul, ← pow_mul, pow_add, mul_right_comm, div_self']
    have h3 := ih (by omega) _ h2
    have h4 := mul_mem h3 (Subgroup.npow_mem_zpowers z (l ^ c * n))
    rwa [div_mul_cancel] at h4

private theorem cyc_abs {A : Type} [CommGroup A] (l : ℕ) (hp : l.Prime)
    (hres : ∀ x : A, x ≠ 1 → ∃ U : Subgroup A, U.index ≠ 0 ∧ x ∉ U)
    (hl : ∀ s t : A, s ^ l = 1 → t ^ l = 1 → s ≠ 1 → ∃ n : ℕ, t = s ^ n) :
    ∃ z : A, (∃ a, z ^ l ^ a = 1) ∧ ∀ s : A, (∃ a, s ^ l ^ a = 1) → ∃ n : ℕ, s = z ^ n := by
  classical
  by_cases hx : ∃ x : A, x ^ l = 1 ∧ x ≠ 1
  · obtain ⟨x, hx1, hx0⟩ := hx
    obtain ⟨U, hU, hxU⟩ := hres x hx0
    let P : ℕ → Prop := fun a => ∃ s : A, s ^ l ^ (a + 1) = 1 ∧ s ^ l ^ a ≠ 1
    have hP0 : P 0 := ⟨x, by simpa using hx1, by simpa using hx0⟩
    have hbd : ∀ a, P a → a ≤ U.index := by
      rintro a ⟨s, h1, h0⟩
      by_contra hlt
      obtain ⟨n, hn⟩ := hl (s ^ l ^ a) x (by rw [← pow_mul, ← pow_succ, h1]) hx1 h0
      apply hxU
      rw [hn]
      apply pow_mem
      have d1 : orderOf (QuotientGroup.mk' U s) ∣ l ^ (a + 1) := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← map_pow, h1, map_one]
      have d2 : orderOf (QuotientGroup.mk' U s) ∣ U.index := orderOf_dvd_natCard _
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 d1
      have d3 : l ^ j ≤ U.index := hj ▸ Nat.le_of_dvd (Nat.pos_of_ne_zero hU) d2
      have d4 : j < l ^ j := Nat.lt_pow_self hp.one_lt
      have d5 : orderOf (QuotientGroup.mk' U s) ∣ l ^ a := hj ▸ pow_dvd_pow l (by omega)
      have d6 := orderOf_dvd_iff_pow_eq_one.1 d5
      rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at d6
      exact d6
    obtain ⟨z, h1, h0⟩ : P (Nat.findGreatest P U.index) := Nat.findGreatest_spec (Nat.zero_le _) hP0
    refine ⟨z, ⟨_, h1⟩, ?_⟩
    rintro s ⟨c, hc⟩
    have key : ∀ c, s ^ l ^ c = 1 → s ^ l ^ (Nat.findGreatest P U.index + 1) = 1 := by
      intro c
      induction c with
      | zero => intro h; simp at h; simp [h]
      | succ c ih =>
        intro h
        by_cases h' : s ^ l ^ c = 1
        · exact ih h'
        · have hPc : P c := ⟨s, h, h'⟩
          have := Nat.le_findGreatest (hbd c hPc) hPc
          exact orderOf_dvd_iff_pow_eq_one.1
            ((orderOf_dvd_of_pow_eq_one h).trans (pow_dvd_pow l (by omega)))
    have hm := gen_of_max l hl _ z h1 h0 _ le_rfl s (key c hc)
    have hf : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.2 ⟨_, pow_pos hp.pos _, h1⟩
    obtain ⟨n, hn⟩ := hf.mem_powers_iff_mem_zpowers.2 hm
    exact ⟨n, hn.symm⟩
  · refine ⟨1, ⟨0, by simp⟩, ?_⟩
    rintro s ⟨c, hc⟩
    refine ⟨0, ?_⟩
    rw [pow_zero]
    induction c with
    | zero => simpa using hc
    | succ c ih =>
      apply ih
      by_contra h
      exact hx ⟨_, by rw [← pow_mul, ← pow_succ, hc], h⟩

theorem UpperTheory.V.Ws.X1.muCyc :
    ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (l : ℕ) [Fact l.Prime] (H : Subgroup Γ), IsClosed (H : Set Γ) → (∀ s ∈ H, ∀ t ∈ H, s ^ l ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → t ^ l ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → s ∉ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → ∃ n : ℕ, t * (s ^ n)⁻¹ ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure) → ∃ ζ, MuGen H (muOf l H) ζ := by
  intro Γ _ _ _ _ _ _ l hp H hH hl
  unfold MuGen muOf
  have hcl : IsClosed (((⁅H, H⁆ : Subgroup Γ).topologicalClosure : Subgroup Γ) : Set Γ) :=
    Subgroup.isClosed_topologicalClosure _
  have hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure :=
    fun a ha b hb => Subgroup.le_topologicalClosure _ (Subgroup.commutator_mem_commutator ha hb)
  generalize (⁅H, H⁆ : Subgroup Γ).topologicalClosure = C at hl hcl hcomm ⊢
  haveI hN : (C.subgroupOf H).Normal := ⟨fun c hc h => by
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    simpa using mul_mem (hcomm h h.2 c c.2) hc⟩
  let π := QuotientGroup.mk' (C.subgroupOf H)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have h1 : ∀ x : H, π x = 1 ↔ (x : Γ) ∈ C := fun x => by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
  have h2 : ∀ x y : H, π x = π y ↔ (x : Γ) * (y : Γ)⁻¹ ∈ C := fun x y => by
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, h1]; simp
  letI : CommGroup (H ⧸ C.subgroupOf H) :=
    { (inferInstance : Group (H ⧸ C.subgroupOf H)) with
      mul_comm := fun a b => by
        obtain ⟨a, rfl⟩ := hπ a
        obtain ⟨b, rfl⟩ := hπ b
        rw [← map_mul, ← map_mul, h2]
        simpa [mul_assoc] using hcomm a a.2 b b.2 }
  refine (cyc_abs (A := H ⧸ C.subgroupOf H) l hp.out ?_ ?_).elim ?_
  rotate_left 2
  · rintro z ⟨⟨a, ha⟩, hz⟩
    obtain ⟨z, rfl⟩ := hπ z
    refine ⟨z, ⟨z.2, a, ?_⟩, ?_⟩
    · rw [← map_pow, h1] at ha
      simpa using ha
    · rintro s ⟨hs, c, hc⟩
      obtain ⟨n, hn⟩ := hz (π ⟨s, hs⟩) ⟨c, by rw [← map_pow, h1]; simpa using hc⟩
      rw [← map_pow, h2] at hn
      exact ⟨n, by simpa using hn⟩
  · intro x hx
    obtain ⟨x, rfl⟩ := hπ x
    have ho : IsOpen {g : Γ | (x : Γ) * g ∉ C} :=
      hcl.isOpen_compl.preimage (continuous_const_mul (x : Γ))
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho
      (by simpa [← h1] using hx)
    refine ⟨(N.toSubgroup.subgroupOf H).map π, ?_, ?_⟩
    · refine ne_zero_of_dvd_ne_zero ?_ (Subgroup.index_map_dvd _ hπ)
      haveI : Finite (Γ ⧸ N.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ N.isOpen'
      haveI : N.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      exact Subgroup.FiniteIndex.index_ne_zero
    · rintro ⟨n, hn, e⟩
      have hn' : (n : Γ)⁻¹ ∈ N.toSubgroup := inv_mem (Subgroup.mem_subgroupOf.1 hn)
      exact hN hn' ((h2 x n).1 e.symm)
  · intro s t hs ht h0
    obtain ⟨s, rfl⟩ := hπ s
    obtain ⟨t, rfl⟩ := hπ t
    rw [← map_pow, h1] at hs ht
    obtain ⟨n, hn⟩ := hl s s.2 t t.2 (by simpa using hs) (by simpa using ht) (by rwa [← h1])
    exact ⟨n, by rw [← map_pow, h2]; simpa using hn⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.PresQuot
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.X1.presQuot :
    ∀ (Λ R' R : Type) [CommRing Λ] [CommRing R'] [Algebra Λ R'] [CommRing R] [Algebra Λ R] (a b : ℕ) (τ : Type) [Finite τ] (g : R' →ₐ[Λ] R) (e : τ → R'), HasPres Λ R' a b → Function.Surjective g → RingHom.ker g = Ideal.span (Set.range e) → HasPres Λ R a (b + Nat.card τ) := by
  intro Λ R' R _ _ _ _ _ a b τ _ g e hP hg he
  obtain ⟨π, f, hπ, hk⟩ := hP
  obtain ⟨σ⟩ : Nonempty (τ ≃ Fin (Nat.card τ)) := ⟨Finite.equivFin τ⟩
  choose l hl using fun t => hπ (e t)
  refine ⟨g.comp π, Fin.append f (l ∘ σ.symm), hg.comp hπ, ?_⟩
  have hrange : Set.range (Fin.append f (l ∘ σ.symm)) = Set.range f ∪ Set.range l := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left i => exact Or.inl ⟨i, by simp⟩
      | right i => exact Or.inr ⟨σ.symm i, by simp⟩
    · rintro (⟨i, rfl⟩ | ⟨t, rfl⟩)
      · exact ⟨Fin.castAdd _ i, by simp⟩
      · exact ⟨Fin.natAdd _ (σ t), by simp⟩
  have hker : RingHom.ker (g.comp π) = Ideal.comap π (RingHom.ker g) := by
    ext x
    simp [RingHom.mem_ker]
  have hmap : Ideal.span (Set.range e) = Ideal.map π (Ideal.span (Set.range l)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext t
    exact (hl t).symm
  rw [hker, he, hmap, Ideal.comap_map_of_surjective π hπ, ← RingHom.ker_eq_comap_bot, hk, hrange,
    Ideal.span_union, sup_comm]
end

