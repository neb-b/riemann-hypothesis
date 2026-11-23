module

public import ReciprocityTheory.DualLattices.Bundle0004
public import ReciprocityTheory.DualLattices.Bundle0005
public import ReciprocityTheory.DualLattices.Bundle0007
public import ReciprocityTheory.DualLattices.Bundle0008

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.CokernelLengthComparisonStatement
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def tPart {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
    [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
    {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} (H : HodgeTateDatum p g v R O σ cp) (a : O) : Submodule R (Ix g → R) :=
  LinearMap.range (Matrix.mulVecLin ((H.ρ a).map (algebraMap ℤ_[p] R)))

def lieDPart {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
    [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
    {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} (H : HodgeTateDatum p g v R O σ cp) (a : O) : Submodule R (Fin g → R) :=
  LinearMap.range (Matrix.mulVecLin (H.ρL a)ᵀ)

abbrev htCoker {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal}
    {R : Type} [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O]
    [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} (H : HodgeTateDatum p g v R O σ cp) (a b : O) :=
  lieDPart H a ⧸ ((tPart H b).map (Matrix.mulVecLin H.Ht)).comap (lieDPart H a).subtype

def CokernelLengthComparisonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ cw cwb : NNReal,
      HasLen v R (htCoker H (e w) (e (π w))) cw →
      HasLen v R (htCoker H (e (π w)) (e w)) cwb → cwb ≤ cw

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.ColengthCotangentBoundStatement
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def ColengthCotangentBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → v (p : C) < 1 →
    ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) →
    ∀ (AA : HopfOrder (C := C) R N) (lenN lenOm : NNReal),
      HasColen R v AA.carrier lenN → HasLen v R (OmAA AA.carrier) lenOm →
      lenN ^ 2 ≤ lenOm ^ Fintype.card N

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.ConstantCoeffRowSubst
section
noncomputable section

open MvPolynomial Matrix Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

theorem rowSubst_X (g : Matrix (Fin ν) (Fin ν) ℂ) (p : Fin ν × ι) :
    rowSubst g (X p) = ∑ l, C (g l p.1) * X (l, p.2) := by
  simp [rowSubst]

theorem rowSubst_C (g : Matrix (Fin ν) (Fin ν) ℂ) (c : ℂ) :
    rowSubst g (C c : MvPolynomial (Fin ν × ι) ℂ) = C c := by
  simp [rowSubst]

theorem constantCoeff_rowSubst (h : Matrix (Fin ν) (Fin ν) ℂ) (Q : MvPolynomial (Fin ν × ι) ℂ) :
    constantCoeff (rowSubst h Q) = constantCoeff Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => rw [rowSubst_C]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p n hp => simp [map_mul, hp, rowSubst_X]

theorem coeff_zero_rowSubst (h : Matrix (Fin ν) (Fin ν) ℂ) (Q : MvPolynomial (Fin ν × ι) ℂ) :
    AddMonoidAlgebra.coeff (rowSubst h Q) 0 = AddMonoidAlgebra.coeff Q 0 := by
  exact constantCoeff_rowSubst h Q

theorem pderiv_rowSubst_X (h : Matrix (Fin ν) (Fin ν) ℂ) (k : Fin ν) (a : ι) (s : Fin ν × ι) :
    pderiv (k, a) (rowSubst h (X s : MvPolynomial (Fin ν × ι) ℂ)) =
      if s.2 = a then C (h k s.1) else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rowSubst_X, map_sum]
  by_cases hs : s.2 = a
  · simp [pderiv_C_mul, pderiv_X, Pi.single_apply, hs]
  · simp [pderiv_C_mul, pderiv_X, Pi.single_apply, hs]

theorem pderiv_rowSubst (h : Matrix (Fin ν) (Fin ν) ℂ) (k : Fin ν) (a : ι)
    (Q : MvPolynomial (Fin ν × ι) ℂ) :
    pderiv (k, a) (rowSubst h Q) = ∑ m, C (h k m) * rowSubst h (pderiv (m, a) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [rowSubst_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have e1 : ∀ m, rowSubst h (pderiv (m, a) (X n : MvPolynomial (Fin ν × ι) ℂ)) =
        if n = (m, a) then 1 else 0 := by
      intro m
      rw [pderiv_X, Pi.single_apply]
      split_ifs <;> simp
    have e2 : ∑ m, C (h k m) * (rowSubst h p * (if n = (m, a) then 1 else 0)) =
        rowSubst h p * (if n.2 = a then C (h k n.1) else 0) := by
      by_cases hn : n.2 = a
      · rw [if_pos hn, Finset.sum_eq_single n.1]
        · rw [if_pos (show n = (n.1, a) from Prod.ext rfl hn)]
          ring
        · intro m _ hm
          rw [if_neg (fun h' => hm (congrArg Prod.fst h').symm)]
          ring
        · intro h'
          exact absurd (Finset.mem_univ _) h'
      · rw [if_neg hn, mul_zero]
        refine Finset.sum_eq_zero (fun m _ => ?_)
        rw [if_neg (fun h' => hn (congrArg Prod.snd h'))]
        ring
    rw [map_mul, Derivation.leibniz, hp, pderiv_rowSubst_X, smul_eq_mul, smul_eq_mul, ← e2,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Derivation.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul, map_mul, map_mul, e1]
    ring

theorem fischer_rowSubst (g : Matrix (Fin ν) (Fin ν) ℂ) (P Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (rowSubst g P) Q = fischer P (rowSubst gᴴ Q) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C c =>
    rw [rowSubst_C, fischer_C_left, fischer_C_left, coeff_zero_rowSubst]
  | add p q hp hq =>
    rw [map_add (f := _), fischer_add_left, fischer_add_left, hp, hq]
  | mul_X p n hp =>
    rcases n with ⟨k, a⟩
    rw [map_mul, rowSubst_X, Finset.mul_sum, fischer_sum_left, fischer_mul_X, pderiv_rowSubst,
      fischer_sum_right]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [mul_left_comm, MvPolynomial.C_mul', fischer_smul_left, fischer_mul_X, hp, MvPolynomial.C_mul',
      fischer_smul_right]
    simp [Matrix.conjTranspose_apply]

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.DiscriminantColengthStatement
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def discr {C : Type} [Field C] {n : ℕ} (a : Fin n → C) : C :=
  ∏ τ, ∏ τ' ∈ Finset.univ.erase τ, (a τ - a τ')

def freeMat {C : Type} [Field C] {n : ℕ} (a : Fin n → C) (h : ℕ) :
    Matrix (Fin n × Fin h) (Fin n × Fin h) C :=
  Matrix.of fun x y => if x.2 = y.2 then a x.1 ^ (y.1 : ℕ) else 0

def sumPts {C : Type} [Field C] {v : Valuation C NNReal} {n s : ℕ}
    (Mτ : Fin n → Lat v (Fin s)) : Set (Fin n × Fin s → C) :=
  {w | ∀ τ, (fun i => w (τ, i)) ∈ (Mτ τ).pts}

def projPts {C : Type} [Field C] {n s : ℕ} (M : Set (Fin n × Fin s → C)) (τ : Fin n) :
    Set (Fin s → C) :=
  (fun w i => w (τ, i)) '' M

def IsLaStable {C : Type} [Field C] {v : Valuation C NNReal} {n s : ℕ} (a : Fin n → C)
    (M : Lat v (Fin n × Fin s)) : Prop :=
  ∀ w ∈ M.pts, (fun y : Fin n × Fin s => a y.1 * w y) ∈ M.pts

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.ExistsFamilyValuationDetEqOne
section
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem cosetCoordinates_sum (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) {ι : Type}
    [Fintype ι] (g : ι → N → C) (x : N) :
    h3co K β (∑ i, g i) x = ∑ i, h3co K β (g i) x := by
  funext l
  simp only [h3co, Finset.sum_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_comm

private theorem hopfOrder_prod_mem_carrier (AA : HopfOrder (C := C) R N) {ι : Type} (s : Finset ι)
    (g : ι → N → C) (h : ∀ i ∈ s, g i ∈ AA.carrier) : ∏ i ∈ s, g i ∈ AA.carrier := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using AA.one_mem
  · intro a s ha ih h
    rw [Finset.prod_insert ha]
    exact AA.mul_mem _ _ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem hopfOrder_const_mem (AA : HopfOrder (C := C) R N) (r : R) :
    (fun _ : N => algebraMap R C r) ∈ AA.carrier := by
  have e : (fun _ : N => algebraMap R C r) = r • (1 : N → C) := by
    funext y
    simp [Algebra.smul_def]
  rw [e]
  exact AA.carrier.smul_mem r AA.one_mem

private theorem hopfOrder_const_sub_mem (AA : HopfOrder (C := C) R N) {n : N → C} (hn : n ∈ AA.carrier)
    (z : N) : (fun y => n z - n y) ∈ AA.carrier := by
  obtain ⟨r, hr⟩ := hopfOrder_exists_algebraMap_eq_of_mem AA hn z
  have e : (fun y => n z - n y) = (fun _ : N => algebraMap R C r) - n := by
    funext y
    simp [hr]
  rw [e]
  exact AA.carrier.sub_mem (hopfOrder_const_mem AA r) hn

private theorem h3co_mul_add_of_coset_invariant (K : AddSubgroup N) [DecidablePred (· ∈ K)]
    (β : Matrix K K C) (a b : N → C) (ha : ∀ y (k : K), a (y + k) = a y)
    (hb : ∀ y (k : K), b (y + k) = b y) (F F' : N → C) (y : N) :
    h3co K β (a * F + b * F') y =
      a y • h3co K β F y + b y • h3co K β F' y := by
  simp only [h3co]
  have e : (fun k : K => (a * F + b * F') (y + k)) =
      a y • (fun k : K => F (y + k)) + b y • (fun k : K => F' (y + k)) := by
    funext k
    simp [ha, hb]
  rw [e, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]

private theorem h3mm_mul_add_of_coset_invariant (K : AddSubgroup N) [DecidablePred (· ∈ K)]
    (β : Matrix K K C) (a b : N → C) (ha : ∀ y (k : K), a (y + k) = a y)
    (hb : ∀ y (k : K), b (y + k) = b y) (G G' : K → N → C) (y : N) :
    h3mm K β (fun j => a * G j + b * G' j) y =
      a y • h3mm K β G y + b y • h3mm K β G' y := by
  ext j l
  simp only [h3mm, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    h3co_mul_add_of_coset_invariant K β a b ha hb, Pi.add_apply, Pi.smul_apply]

private theorem hopfOrder_det_fun_mem (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) =
      Submodule.span R (Set.range fun j k => β k j))
    (G : K → N → C) (hG : ∀ j, G j ∈ AA.carrier) :
    (fun y => (h3mm K β G y).det) ∈ AA.carrier := by
  have h := (det_mem_and_adjugate_mem AA
    (Matrix.of fun i j => fun y => h3co K β (G i) y j)
    (fun i j => cosetCoordinates_mem AA K β hβ hAK (hG i) j)).1
  have e : ∀ y, (Matrix.of fun i j => fun y => h3co K β (G i) y j).map
      (fun g => g y) = h3mm K β G y := fun y => by
    ext i j
    rfl
  simpa only [e] using h

private theorem hopfOrder_norm_fun_mem (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) =
      Submodule.span R (Set.range fun j k => β k j))
    (G : K → N → C) (hG : ∀ j, G j ∈ AA.carrier) :
    (fun y => ∏ k : K, (h3mm K β G (y + k)).det) ∈ AA.carrier := by
  have e : (fun y => ∏ k : K, (h3mm K β G (y + k)).det) =
      ∏ k : K, (fun y => (h3mm K β G (y + k)).det) := by
    funext y
    simp only [Finset.prod_apply]
  rw [e]
  exact hopfOrder_prod_mem_carrier AA _ _ fun k _ =>
    hopfOrder_translate_mem AA (hopfOrder_det_fun_mem AA K β hβ hAK G hG) (k : N)

private theorem valuation_sub_eq_one_of_eq_one_of_lt_one {a b : C} (ha : v a = 1) (hb : v b < 1) :
    v (a - b) = 1 := by
  have h : v (-b) < v a := by
    rw [Valuation.map_neg, ha]
    exact hb
  rw [sub_eq_add_neg, v.map_add_eq_of_lt_left h, ha]

private theorem nnreal_pow_lt_one_of_lt_one_of_ne_zero {a : NNReal} (hlt : a < 1) {m : ℕ} (hm : m ≠ 0) :
    a ^ m < 1 := by
  have h0 : (0 : NNReal) ≤ a := by positivity
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [pow_succ]
  refine lt_of_le_of_lt (mul_le_of_le_one_left h0 ?_) hlt
  exact pow_le_one₀ h0 hlt.le

theorem exists_family_valuation_det_eq_one (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j)) :
    ∃ f : K → N → C, (∀ j, f j ∈ AA.carrier) ∧ ∀ x, v (h3mm K β f x).det = 1 := by
  classical
  have hlift : ∀ j : K, ∃ f ∈ AA.carrier, ∀ k : K, f k = β k j := by
    intro j
    have hmem : (fun k : K => β k j) ∈ AA.carrier.map (resK (R := R) K) := by
      rw [hAK]
      exact Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨f, hf, hfe⟩ := Submodule.mem_map.mp hmem
    exact ⟨f, hf, fun k => congrFun hfe k⟩
  choose f0 hf0 hf0e using hlift
  have hgood : ∀ x : N,
      v (h3mm K β (fun j y => f0 j (y + -x)) x).det = 1 := by
    intro x
    have e : h3mm K β (fun j y => f0 j (y + -x)) x = (β⁻¹ * β)ᵀ := by
      ext j l
      have h1 : (fun k : K => f0 j (x + (k : N) + -x)) = fun k => β k j := by
        funext k
        rw [show x + (k : N) + -x = k by abel]
        exact hf0e j k
      show (β⁻¹ *ᵥ fun k : K => f0 j (x + (k : N) + -x)) l = (β⁻¹ * β) l j
      rw [h1]
      rfl
    rw [e, Matrix.nonsing_inv_mul β hβ, Matrix.transpose_one, Matrix.det_one, map_one]
  have key : ∀ S : Finset N, ∃ G : K → N → C, (∀ j, G j ∈ AA.carrier) ∧
      ∀ z ∈ S, v (h3mm K β G z).det = 1 := by
    intro S
    refine Finset.induction_on S ⟨fun _ => 0, fun _ => AA.carrier.zero_mem, by simp⟩ ?_
    intro x S hx ih
    obtain ⟨G, hG, hS⟩ := ih
    by_cases hGx : v (h3mm K β G x).det = 1
    · refine ⟨G, hG, fun z hz => ?_⟩
      rcases Finset.mem_insert.mp hz with hzx | hz
      · rw [hzx]
        exact hGx
      · exact hS z hz
    obtain ⟨n, hn_def⟩ : ∃ n : N → C,
        n = fun y => ∏ k : K, (h3mm K β G (y + k)).det := ⟨_, rfl⟩
    have hnmem : n ∈ AA.carrier := by
      rw [hn_def]
      exact hopfOrder_norm_fun_mem AA K β hβ hAK G hG
    have hninv : ∀ y (k0 : K), n (y + k0) = n y := by
      intro y k0
      simp only [hn_def]
      exact Fintype.prod_equiv (Equiv.addLeft k0) _ _ (fun k => by simp [add_assoc])
    have hvn : ∀ y, v (n y) = v (h3mm K β G y).det ^ Fintype.card K := by
      intro y
      simp only [hn_def]
      rw [map_prod, Finset.prod_congr rfl (fun k _ =>
        valuation_det_cosetCoordinateMatrix_add hv AA K β hβ hAK G y k),
        Finset.prod_const, Finset.card_univ]
    have hDle : ∀ y, v (h3mm K β G y).det ≤ 1 := fun y =>
      valuation_det_le_one_of_entries_integral hv _ (fun i j =>
        hopfOrder_exists_algebraMap_eq_of_mem AA (cosetCoordinates_mem AA K β hβ hAK (hG i) j) y)
    have : Nonempty K := ⟨0⟩
    have hcard : Fintype.card K ≠ 0 := Fintype.card_ne_zero
    have hnS : ∀ z ∈ S, v (n z) = 1 := fun z hz => by
      rw [hvn, hS z hz, one_pow]
    have hnx : v (n x) < 1 := by
      rw [hvn]
      exact nnreal_pow_lt_one_of_lt_one_of_ne_zero (lt_of_le_of_ne (hDle x) hGx) hcard
    obtain ⟨a, ha_def⟩ : ∃ a : N → C, a = fun y => n x - n y := ⟨_, rfl⟩
    obtain ⟨b, hb_def⟩ : ∃ b : N → C, b = fun y => ∏ w ∈ S, (n w - n y) := ⟨_, rfl⟩
    obtain ⟨g, hg_def⟩ : ∃ g : K → N → C, g = fun j y => f0 j (y + -x) := ⟨_, rfl⟩
    have hamem : a ∈ AA.carrier := by
      rw [ha_def]
      exact hopfOrder_const_sub_mem AA hnmem x
    have hbmem : b ∈ AA.carrier := by
      have e : (fun y => ∏ w ∈ S, (n w - n y)) = ∏ w ∈ S, (fun y => n w - n y) := by
        funext y
        simp only [Finset.prod_apply]
      rw [hb_def, e]
      exact hopfOrder_prod_mem_carrier AA S _ (fun w _ => hopfOrder_const_sub_mem AA hnmem w)
    have hgmem : ∀ j, g j ∈ AA.carrier := by
      intro j
      rw [hg_def]
      exact hopfOrder_translate_mem AA (hf0 j) (-x)
    have hgx : v (h3mm K β g x).det = 1 := by
      rw [hg_def]
      exact hgood x
    have hainv : ∀ y (k : K), a (y + k) = a y := by
      intro y k
      simp only [ha_def, hninv]
    have hbinv : ∀ y (k : K), b (y + k) = b y := by
      intro y k
      simp only [hb_def, hninv]
    refine ⟨fun j => a * G j + b * g j, fun j => AA.carrier.add_mem
      (AA.mul_mem _ _ hamem (hG j)) (AA.mul_mem _ _ hbmem (hgmem j)), fun z hz => ?_⟩
    rw [h3mm_mul_add_of_coset_invariant K β a b hainv hbinv G g z]
    rcases Finset.mem_insert.mp hz with hzx | hz
    · rw [hzx]
      have ha0 : a x = 0 := by simp only [ha_def, sub_self]
      have hb1 : v (b x) = 1 := by
        simp only [hb_def]
        rw [map_prod]
        exact Finset.prod_eq_one (fun w hw => valuation_sub_eq_one_of_eq_one_of_lt_one (hnS w hw) hnx)
      rw [ha0, zero_smul, zero_add, Matrix.det_smul, map_mul, map_pow, hgx, hb1, one_pow,
        mul_one]
    · have hb0 : b z = 0 := by
        simp only [hb_def]
        exact Finset.prod_eq_zero hz (sub_self _)
      have ha1 : v (a z) = 1 := by
        simp only [ha_def]
        rw [Valuation.map_sub_swap]
        exact valuation_sub_eq_one_of_eq_one_of_lt_one (hnS z hz) hnx
      rw [hb0, zero_smul, add_zero, Matrix.det_smul, map_mul, map_pow, hS z hz, ha1, one_pow,
        mul_one]
  obtain ⟨G, hG, hGall⟩ := key Finset.univ
  exact ⟨G, hG, fun x => hGall x (Finset.mem_univ x)⟩

end ReciprocityTheory.PGsh.L2
end
end

-- bundled from ReciprocityTheory.DualLattices.IsotypicAveragingStatement
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def IsotypicAveragingStatement : Prop :=
  ∀ (S : Type) [CommRing S] (g m : ℕ) (Ht Bt : Matrix (Fin g) (Ix g) S)
    (E : Matrix (Ix g) (Ix g) S) (cp : S)
    (εT : Fin m → Matrix (Ix g) (Ix g) S) (εL : Fin m → Matrix (Fin g) (Fin g) S)
    (π : Equiv.Perm (Fin m)),
    (∀ i, π (π i) = i) →
    (∀ i j, εT i * εT j = if i = j then εT i else 0) → ∑ i, εT i = 1 →
    (∀ i j, εL i * εL j = if i = j then εL i else 0) → ∑ i, εL i = 1 →
    (∀ i, Ht * εT i = (εL (π i))ᵀ * Ht) →
    (∀ i, (εT i)ᵀ * E = E * εT (π i)) →
    Btᵀ * Ht - Htᵀ * Bt = cp • E →
    let Bt' := ∑ i, εL i * Bt * εT i
    (Bt'ᵀ * Ht - Htᵀ * Bt' = cp • E) ∧ (∀ i, Bt' * εT i = εL i * Bt') ∧
    (Matrix.fromRows Ht Bt').det ^ 2 = cp ^ (2 * g) * E.det

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.MonomialDeterminantStatement
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def MonomialDeterminantStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal) (R : Type)
    [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R) (u : ι → (ι → ZMod p) → C),
    IsUnit Λ.det → (∀ j x, v (u j x) ≤ 1) →
    (∀ j x, v (u j x - algebraMap R C (∑ i, Λ j i * ((x i).val : R))) < 1) →
    v (Matrix.of fun (x α : ι → ZMod p) => ∏ j, u j x ^ (α j).val).det = 1 ∧
    ∀ ε : ι → C,
      v (Matrix.of fun (x α : ι → ZMod p) => ∏ j, (ε j * u j x) ^ (α j).val).det =
        ∏ j, v (ε j) ^ (p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2))

end ReciprocityTheory.PGsh.Up
end
end

