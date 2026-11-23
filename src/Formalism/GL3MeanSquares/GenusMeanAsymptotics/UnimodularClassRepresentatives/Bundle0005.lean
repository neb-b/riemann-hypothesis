module

public import Mathlib
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFiberMulCardRange
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0002

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemRangeLinPart
section
namespace Formalism.HermitianLattices.Ext.L3.SecondPropositionFree

open NormLifting

variable {A B : Type*} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {π : A →+* B}

theorem card_lift_pred [Finite A] (hπ : Function.Surjective π) (hστ : ∀ a, π (σ a) = τ (π a))
    (hσ : ∀ a, σ (σ a) = a) (hsq : ∀ a b, π a = 0 → π b = 0 → a * b = 0) {θ e : A}
    (he : (θ - σ θ) * e = 1) {n : A} (hn : σ n = n) (q : ℕ)
    (hq : Nat.card A = q ^ 2 * Nat.card B) (M : ℕ) (hM : 1 ≤ M) (p : (Fin M → B) → Prop)
    (hsurj : ∀ y : Fin M → A, p (fun i => π (y i)) → ∀ w ∈ fixSub σ (RingHom.ker π),
      w ∈ (linPart σ (RingHom.ker π) y).range) :
    Nat.card {x : Fin M → A // p (fun i => π (x i)) ∧ ∑ i, σ (x i) * x i = n} =
      q ^ (2 * M - 1) * Nat.card {x : Fin M → B // p x ∧ ∑ i, τ (x i) * x i = π n} := by
  classical
  have hIσ : ∀ a ∈ RingHom.ker π, σ a ∈ RingHom.ker π := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    rw [hστ, ha, map_zero]
  haveI : Finite B := Finite.of_surjective π hπ

  have hker : Nat.card (RingHom.ker π) = q ^ 2 := by
    have h1 : Nat.card A = Nat.card (RingHom.ker π) * Nat.card B := by
      refine card_eq_mul_of_fibers π _ (fun b => ?_)
      obtain ⟨a0, ha0⟩ := hπ b
      exact Nat.card_congr
        { toFun := fun a => ⟨a.1 - a0, by rw [RingHom.mem_ker, map_sub, a.2, ha0, sub_self]⟩
          invFun := fun k => ⟨k.1 + a0, by rw [map_add (f := _), RingHom.mem_ker.mp k.2, ha0, zero_add]⟩
          left_inv := fun a => Subtype.ext (sub_add_cancel a.1 a0)
          right_inv := fun k => Subtype.ext (add_sub_cancel_right k.1 a0) }
    have hB : 0 < Nat.card B := Nat.card_pos
    rw [hq] at h1
    exact (Nat.eq_of_mul_eq_mul_right hB h1).symm
  have hq0 : 0 < q := by
    have hk : 0 < Nat.card (RingHom.ker π) := Nat.card_pos
    rw [hker] at hk
    exact Nat.pos_of_ne_zero (fun h => by simp [h] at hk)

  have hfix : Nat.card (fixSub σ (RingHom.ker π)) = q := by
    have h := card_fixSub_sq hσ hIσ he
    rw [hker] at h
    exact Nat.pow_left_injective two_ne_zero h

  have hrange : ∀ x0 : Fin M → A, p (fun i => π (x0 i)) →
      Nat.card (linPart σ (RingHom.ker π) x0).range = q := by
    intro x0 hp
    have hR : (linPart σ (RingHom.ker π) x0).range = fixSub σ (RingHom.ker π) := by
      ext w
      rw [AddMonoidHom.mem_range]
      constructor
      · rintro ⟨δ, rfl⟩
        show linPart σ (RingHom.ker π) x0 δ ∈ RingHom.ker π ∧
          σ (linPart σ (RingHom.ker π) x0 δ) = linPart σ (RingHom.ker π) x0 δ
        refine ⟨?_, ?_⟩
        · rw [linPart_apply]
          refine Ideal.sum_mem _ fun i _ => Ideal.add_mem _ ?_ ?_
          · exact Ideal.mul_mem_left _ _ (δ i).2
          · exact Ideal.mul_mem_right _ _ (hIσ _ (δ i).2)
        · set_option synthInstance.maxHeartbeats 100000 in
            rw [linPart_apply, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [map_add (f := _), map_mul, hσ]
          ring
      · intro hw
        exact AddMonoidHom.mem_range.mp (hsurj x0 hp w hw)
    rw [hR, hfix]

  have hnorm : ∀ x : Fin M → A, ∑ i, σ (x i) * x i = n → ∑ i, τ (π (x i)) * π (x i) = π n := by
    intro x hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hx, map_sum]
    simp only [map_mul, hστ]
  refine card_eq_mul_of_fibers
    (fun x : {x : Fin M → A // p (fun i => π (x i)) ∧ ∑ i, σ (x i) * x i = n} =>
      (⟨fun i => π (x.1 i), x.2.1, hnorm x.1 x.2.2⟩ :
        {x : Fin M → B // p x ∧ ∑ i, τ (x i) * x i = π n})) _ ?_
  intro y
  choose x0 hx0 using fun i => hπ (y.1 i)
  have hpx0 : p (fun i => π (x0 i)) := by
    have h : (fun i => π (x0 i)) = y.1 := funext hx0
    rw [h]
    exact y.2.1
  have hNx0 : π (∑ i, σ (x0 i) * x0 i) = π n := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul, hστ, hx0]
    exact y.2.2
  have ht : n - ∑ i, σ (x0 i) * x0 i ∈ fixSub σ (RingHom.ker π) := by
    show n - ∑ i, σ (x0 i) * x0 i ∈ RingHom.ker π ∧
      σ (n - ∑ i, σ (x0 i) * x0 i) = n - ∑ i, σ (x0 i) * x0 i
    refine ⟨?_, ?_⟩
    · rw [RingHom.mem_ker, map_sub, hNx0, sub_self]
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, hn, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_mul, hσ]
      ring

  have key : Nat.card {δ : Fin M → RingHom.ker π //
      linPart σ (RingHom.ker π) x0 δ = n - ∑ i, σ (x0 i) * x0 i} = q ^ (2 * M - 1) := by
    have hfib := card_fiber_mul_card_range (linPart σ (RingHom.ker π) x0) _ (hsurj x0 hpx0 _ ht)
    rw [hrange x0 hpx0, Nat.card_fun, hker, Nat.card_eq_fintype_card (α := Fin M), Fintype.card_fin,
      ← pow_mul] at hfib
    have hpow : q ^ (2 * M) = q ^ (2 * M - 1) * q := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow] at hfib
    exact Nat.eq_of_mul_eq_mul_right hq0 hfib

  have hfwd : ∀ x : Fin M → A, (∀ i, π (x i) = y.1 i) → ∀ i, x i - x0 i ∈ RingHom.ker π := by
    intro x hx i
    rw [RingHom.mem_ker, map_sub, hx, hx0, sub_self]
  have hexp : ∀ (x : Fin M → A) (hd : ∀ i, x i - x0 i ∈ RingHom.ker π),
      ∑ i, σ (x i) * x i = ∑ i, σ (x0 i) * x0 i +
        linPart σ (RingHom.ker π) x0 (fun i => ⟨x i - x0 i, hd i⟩) := by
    intro x hd
    rw [linPart_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h0 : σ (x i - x0 i) * (x i - x0 i) = 0 :=
      hsq _ _ (RingHom.mem_ker.mp (hIσ _ (hd i))) (RingHom.mem_ker.mp (hd i))
    dsimp only
    rw [map_sub] at h0 ⊢
    linear_combination h0
  have hLfwd : ∀ (x : Fin M → A) (hx : ∀ i, π (x i) = y.1 i), ∑ i, σ (x i) * x i = n →
      linPart σ (RingHom.ker π) x0 (fun i => ⟨x i - x0 i, hfwd x hx i⟩) =
        n - ∑ i, σ (x0 i) * x0 i := by
    intro x hx hN
    have h := hexp x (hfwd x hx)
    rw [hN] at h
    rw [h]
    ring
  have hdmem : ∀ (δ : Fin M → RingHom.ker π) i, (x0 i + δ i) - x0 i ∈ RingHom.ker π := by
    intro δ i
    rw [add_sub_cancel_left]
    exact (δ i).2
  have hbinv : ∀ (δ : Fin M → RingHom.ker π) i, π (x0 i + δ i) = y.1 i := by
    intro δ i
    rw [map_add (f := _), RingHom.mem_ker.mp (δ i).2, add_zero, hx0]
  have hpinv : ∀ δ : Fin M → RingHom.ker π, p (fun i => π (x0 i + δ i)) := by
    intro δ
    have h : (fun i => π (x0 i + δ i)) = y.1 := funext (hbinv δ)
    rw [h]
    exact y.2.1
  have hNinv : ∀ δ : Fin M → RingHom.ker π,
      linPart σ (RingHom.ker π) x0 δ = n - ∑ i, σ (x0 i) * x0 i →
        ∑ i, σ (x0 i + δ i) * (x0 i + δ i) = n := by
    intro δ hδ
    have h := hexp (fun i => x0 i + δ i) (hdmem δ)
    have hδ' : (fun i => (⟨(x0 i + δ i) - x0 i, hdmem δ i⟩ : RingHom.ker π)) = δ := by
      funext i
      exact Subtype.ext (add_sub_cancel_left (x0 i) (δ i : A))
    rw [hδ', hδ] at h
    rw [h]
    ring
  rw [← key]
  exact Nat.card_congr
    { toFun := fun x => ⟨fun i => ⟨x.1.1 i - x0 i,
          hfwd x.1.1 (fun j => congrFun (congrArg Subtype.val x.2) j) i⟩,
        hLfwd x.1.1 (fun j => congrFun (congrArg Subtype.val x.2) j) x.1.2.2⟩
      invFun := fun δ => ⟨⟨fun i => x0 i + δ.1 i, hpinv δ.1, hNinv δ.1 δ.2⟩,
        Subtype.ext (funext fun i => hbinv δ.1 i)⟩
      left_inv := fun x => Subtype.ext (Subtype.ext (funext fun i =>
        show x0 i + (x.1.1 i - x0 i) = x.1.1 i by ring))
      right_inv := fun δ => Subtype.ext (funext fun i => Subtype.ext
        (show x0 i + (δ.1 i : A) - x0 i = (δ.1 i : A) by ring)) }

theorem mem_range_linPart (I : Ideal A) {M : ℕ} (y : Fin M → A) (i₀ : Fin M)
    {b : A} (hb : σ (y i₀) * b + σ b * y i₀ = 1) {w : A} (hw : w ∈ fixSub σ I) :
    w ∈ (linPart σ I y).range := by
  have hw' : w ∈ I ∧ σ w = w := hw
  obtain ⟨hwI, hσw⟩ := hw'
  classical
  refine ⟨fun i => if i = i₀ then ⟨b * w, I.mul_mem_left b hwI⟩ else 0, ?_⟩
  rw [linPart_apply, Finset.sum_eq_single i₀]
  · rw [if_pos rfl]
    show σ (y i₀) * (b * w) + σ (b * w) * y i₀ = w
    rw [map_mul, hσw]
    linear_combination w * hb
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

end Formalism.HermitianLattices.Ext.L3.SecondPropositionFree
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.PolNatDegreeLe
section
open Matrix Polynomial

namespace Formalism.HermitianLattices.Ext.L3.HU

variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Node

theorem div_mem (hS : IsLocUnif S ϖ) : ∀ (l : ℕ) (f : K), f ∈ S → star f = f →
    f * (ϖ⁻¹) ^ (l + 1) ∉ S → ϖ ^ l * f⁻¹ ∈ S := by
  intro l
  induction l with
  | zero =>
    intro f hf hs hn
    rcases hS.dv f hf hs with h | h
    · simpa using h
    · exact absurd (by simpa using h) hn
  | succ l ih =>
    intro f hf hs hn
    rcases hS.dv f hf hs with h | h
    · rw [pow_succ, mul_assoc]
      exact S.mul_mem (S.pow_mem hS.mem _) (S.mul_mem hS.mem h)
    · have hgs : star (f * ϖ⁻¹) = f * ϖ⁻¹ := by
        rw [star_mul', star_inv₀, hS.fix, hs]
      have hgn : f * ϖ⁻¹ * (ϖ⁻¹) ^ (l + 1) ∉ S := by
        rwa [mul_assoc, ← pow_succ']
      have := ih (f * ϖ⁻¹) h hgs hgn
      rw [mul_inv, inv_inv] at this
      have e : ϖ ^ (l + 1) * f⁻¹ = ϖ ^ l * (f⁻¹ * ϖ) := by ring
      rw [e]
      exact this

theorem exists_pow (hS : IsLocUnif S ϖ) {ι : Type*} (s : Finset ι) (a : ι → K) :
    ∃ l : ℕ, ∀ i ∈ s, ϖ ^ l * a i ∈ S := by
  choose L hL using hS.arch
  refine ⟨∑ i ∈ s, L (a i), fun i hi => ?_⟩
  have hle : L (a i) ≤ ∑ j ∈ s, L (a j) :=
    Finset.single_le_sum (f := fun j => L (a j)) (fun _ _ => Nat.zero_le _) hi
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact S.mul_mem (S.pow_mem hS.mem _) (hL _)

noncomputable def pol (A B : Matrix n n K) : K[X] := det ((X : K[X]) • A.map C + B.map C)

theorem pol_eval (A B : Matrix n n K) (c : K) : (pol A B).eval c = det (c • A + B) := by
  unfold pol
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.smul_apply]
  ring

theorem pol_natDegree_le (A B : Matrix n n K) : (pol A B).natDegree ≤ Fintype.card n :=
  Polynomial.natDegree_det_X_add_C_le A B

end Node

theorem exists_node [CharZero K] (hS : IsLocUnif S ϖ) (n : Type*) [Fintype n] [DecidableEq n] :
    ∃ l : ℕ, ∀ X : Matrix n n K, Ent S X → X.det ≠ 0 → X.det⁻¹ ∈ S →
      ∃ c ∈ S, c + star c = 1 ∧ ∃ W' : Matrix n n K, Ent S W' ∧
        (c • (1 : Matrix n n K) + star c • X) * W' = ϖ ^ l • (1 : Matrix n n K) := by
  obtain ⟨τ, hτS, hτ⟩ := hS.tr
  obtain ⟨θ, hθS, hθs, hθ0⟩ := hS.skew
  have hdetS : ∀ M : Matrix n n K, Ent S M → M.det ∈ S := by
    intro M hM
    have e : M = S.subtype.mapMatrix (Matrix.of fun i j => (⟨M i j, hM i j⟩ : S)) := by
      ext i j; rfl
    rw [e, ← RingHom.map_det]
    exact SetLike.coe_mem _
  have hadjS : ∀ M : Matrix n n K, Ent S M → Ent S M.adjugate := by
    intro M hM i j
    have e : M = S.subtype.mapMatrix (Matrix.of fun i j => (⟨M i j, hM i j⟩ : S)) := by
      ext i j; rfl
    rw [e, ← RingHom.map_adjugate]
    exact SetLike.coe_mem _
  have hnot : ϖ⁻¹ ∉ S := by
    intro h
    have := (hS.rad (-ϖ⁻¹) (S.neg_mem h)).1
    apply this
    rw [mul_neg, mul_inv_cancel₀ hS.ne]
    ring
  let N := Fintype.card n
  let s : Finset ℕ := Finset.range (2 * N + 1)
  let v : ℕ → K := fun k => τ + (k : K) * θ
  have hv : Set.InjOn v s := by
    intro a _ b _ hab
    have h1 : (a : K) * θ = (b : K) * θ := add_left_cancel hab
    exact_mod_cast mul_right_cancel₀ hθ0 h1
  have hvS : ∀ k, v k ∈ S := fun k => S.add_mem hτS (S.mul_mem (natCast_mem S k) hθS)
  have hvs : ∀ k, star (v k) = 1 - v k := by
    intro k
    simp only [v, star_add, star_mul', star_natCast, hθs]
    linear_combination hτ
  obtain ⟨l, hl⟩ := Node.exists_pow hS s (fun k => (Lagrange.basis s v k).eval 1)
  refine ⟨l, fun X hX hd hdi => ?_⟩
  let R : K[X] := Node.pol (1 - X) X * Node.pol (Xᴴ - 1) 1
  have hRdeg : R.degree < (s.card : WithBot ℕ) := by
    have h1 : R.natDegree ≤ 2 * N := by
      refine (Polynomial.natDegree_mul_le).trans ?_
      rw [two_mul]
      exact add_le_add (Node.pol_natDegree_le _ _) (Node.pol_natDegree_le _ _)
    refine lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le h1) ?_
    simp only [s, Finset.card_range]
    exact_mod_cast Nat.lt_succ_self _
  have hReval : ∀ c : K, star c = 1 - c →
      R.eval c = (c • (1 : Matrix n n K) + star c • X).det *
        star ((c • (1 : Matrix n n K) + star c • X).det) := by
    intro c hc
    rw [Polynomial.eval_mul, Node.pol_eval, Node.pol_eval, ← Matrix.det_conjTranspose]
    congr 2
    · rw [hc, smul_sub, sub_smul, one_smul]; abel
    · simp only [conjTranspose_add, conjTranspose_smul, conjTranspose_one, star_star]
      rw [hc, smul_sub, sub_smul, one_smul]; abel
  have hR1 : R.eval 1 = star X.det := by
    simp only [R]
    rw [Polynomial.eval_mul, Node.pol_eval, Node.pol_eval]
    simp [Matrix.det_conjTranspose]
  have hsum : R.eval 1 = ∑ k ∈ s, R.eval (v k) * (Lagrange.basis s v k).eval 1 := by
    conv_lhs => rw [Lagrange.eq_interpolate hv hRdeg]
    rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
    simp [Polynomial.eval_mul, Polynomial.eval_C]
  have hX0 : X.det ≠ 0 := hd
  have hR1S : (R.eval 1)⁻¹ ∈ S := by
    rw [hR1, ← star_inv₀]
    exact hS.star_mem _ hdi
  have hR10 : R.eval 1 ≠ 0 := by
    rw [hR1]; exact star_ne_zero.mpr hX0
  have hMS : ∀ k, Ent S (v k • (1 : Matrix n n K) + star (v k) • X) := by
    intro k i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    refine S.add_mem (S.mul_mem (hvS k) ?_) (S.mul_mem (hS.star_mem _ (hvS k)) (hX i j))
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  have hex : ∃ k ∈ s, R.eval (v k) * (ϖ⁻¹) ^ (l + 1) ∉ S := by
    by_contra hcon
    push_neg at hcon
    apply hnot
    have h1 : R.eval 1 * ϖ⁻¹ ∈ S := by
      have e : R.eval 1 * ϖ⁻¹ =
          ∑ k ∈ s, (R.eval (v k) * (ϖ⁻¹) ^ (l + 1)) * (ϖ ^ l * (Lagrange.basis s v k).eval 1) := by
        rw [hsum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        have e1 : ϖ ^ l * (ϖ⁻¹) ^ (l + 1) = ϖ⁻¹ := by
          rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hS.ne, one_pow, one_mul]
        linear_combination (-(Polynomial.eval (v k) R * Polynomial.eval 1 (Lagrange.basis s v k))) * e1
      rw [e]
      exact S.sum_mem fun k hk => S.mul_mem (hcon k hk) (hl k hk)
    have e2 : ϖ⁻¹ = (R.eval 1)⁻¹ * (R.eval 1 * ϖ⁻¹) := by
      field_simp
    rw [e2]
    exact S.mul_mem hR1S h1
  obtain ⟨k, hk, hkn⟩ := hex
  set M := v k • (1 : Matrix n n K) + star (v k) • X with hMdef
  have hfk : R.eval (v k) = M.det * star M.det := hReval (v k) (hvs k)
  have hfS : R.eval (v k) ∈ S := by
    rw [hfk]; exact S.mul_mem (hdetS M (hMS k)) (hS.star_mem _ (hdetS M (hMS k)))
  have hfs : star (R.eval (v k)) = R.eval (v k) := by
    rw [hfk, star_mul', star_star, mul_comm]
  have hf0 : R.eval (v k) ≠ 0 := by
    intro h0; apply hkn; rw [h0, zero_mul]; exact S.zero_mem
  have hdiv := Node.div_mem hS l _ hfS hfs hkn
  have hM0 : M.det ≠ 0 := by
    intro h0; apply hf0; rw [hfk, h0, zero_mul]
  have hcS : ϖ ^ l * M.det⁻¹ ∈ S := by
    have e : ϖ ^ l * M.det⁻¹ = ϖ ^ l * (R.eval (v k))⁻¹ * star M.det := by
      rw [hfk]
      have : star M.det ≠ 0 := star_ne_zero.mpr hM0
      field_simp
    rw [e]
    exact S.mul_mem hdiv (hS.star_mem _ (hdetS M (hMS k)))
  refine ⟨v k, hvS k, by rw [hvs k]; ring, (ϖ ^ l * M.det⁻¹) • M.adjugate, ?_, ?_⟩
  · intro i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact S.mul_mem hcS (hadjS M (hMS k) i j)
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
    congr 1
    rw [← hMdef]
    field_simp

end Formalism.HermitianLattices.Ext.L3.HU
end

