module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0001
public import ReciprocityTheory.ReductiveGroups.Models.FiniteGeneration.FiniteGenerationProofs.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ETGMulQ
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB.G2.Gen

open ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {S : Type} [CommRing S] {ι : Type}
  (D : ι → S → S) (κ : k →+* S)
  (hadd : ∀ l f g, D l (f + g) = D l f + D l g) (hC : ∀ l a, D l (κ a) = 0)
  (hmul : ∀ l f g, D l (f * g) = D l f * g + f * D l g)

def TG (w : List ι) (A : S) : S := w.foldr (fun l g => D l g) A

include hadd in
theorem D_zero (l : ι) : D l 0 = 0 := by
  simpa using hadd l 0 0

include hadd in
theorem D_list_sum (l : ι) (L : List S) : D l L.sum = (L.map (D l)).sum := by
  induction L with
  | nil => simpa using D_zero D hadd l
  | cons a L ih => simp [hadd, ih]

theorem TG_append (w w' : List ι) (A : S) : TG D (w ++ w') A = TG D w (TG D w' A) := by
  simp only [TG, List.foldr_append]

include hadd in
theorem TG_add (w : List ι) (A B : S) : TG D w (A + B) = TG D w A + TG D w B := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    show D l (TG D w (A + B)) = D l (TG D w A) + D l (TG D w B)
    rw [ih, hadd]

include hadd hmul in
theorem TG_mul (w : List ι) (A B : S) :
    TG D w (A * B) = ((splits w).map (fun p => TG D p.1 A * TG D p.2 B)).sum := by
  induction w with
  | nil => simp [TG, splits]
  | cons l w ih =>
    have e : ∀ (v : List ι) (X : S), TG D (l :: v) X = D l (TG D v X) := fun _ _ => rfl
    rw [e, ih, D_list_sum D hadd]
    simp only [splits, List.map_append, List.sum_append, List.map_map, Function.comp_def, e, hmul,
      List.sum_map_add]

section Q
variable (e : S →+* k) (c : ι → ι → k) (q : S)
  (hq0 : e q = 0) (hq1 : ∀ l, e (D l q) = 0) (hq2 : ∀ l l', D l (D l' q) = κ (c l l'))

include hadd hC hq2 in
theorem TG_q_long (w : List ι) (hw : 3 ≤ w.length) : TG D w q = 0 := by
  induction w with
  | nil => simp at hw
  | cons l w ih =>
    show D l (TG D w q) = 0
    rcases Nat.lt_or_ge w.length 3 with h | h
    · have h2 : w.length = 2 := by
        simp only [List.length_cons] at hw
        omega
      obtain ⟨y, z, rfl⟩ := List.length_eq_two.mp h2
      show D l (D y (D z q)) = 0
      rw [hq2, hC]
    · rw [ih h, D_zero D hadd]

variable (he : ∀ a, e (κ a) = a)

include hadd hC hq0 hq1 hq2 he in
theorem e_TG_q (b : List ι) : e (TG D b q) = ev2 c b := by
  match b with
  | [] => exact hq0
  | [x] => exact hq1 x
  | [x, y] =>
    show e (D x (D y q)) = c x y
    rw [hq2, he]
  | x :: y :: z :: r =>
    rw [TG_q_long (D := D) (κ := κ) (hadd := hadd) (hC := hC) (c := c) (q := q) (hq2 := hq2)
      (w := x :: y :: z :: r) (by simp)]
    exact map_zero e

include hadd hmul hC hq0 hq1 hq2 he in
theorem e_TG_mul_q (w : List ι) (A : S) :
    e (TG D w (A * q)) = ((splits w).map (fun p => e (TG D p.1 A) * ev2 c p.2)).sum := by
  simp only [TG_mul (D := D) (hadd := hadd) (hmul := hmul), map_list_sum, List.map_map,
    Function.comp_def, map_mul, e_TG_q (D := D) (κ := κ) (hadd := hadd) (hC := hC) (e := e) (c := c)
      (q := q) (hq0 := hq0) (hq1 := hq1) (hq2 := hq2) (he := he)]

end Q

end ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ExpLaw
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

variable {k : Type} [CommRing k] [Algebra ℚ k]

def ExpLawSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (ℓ : Pt k 1 d), (∀ i, constantCoeff (ℓ i) = 0) →
    dLin ℓ = 1 →
    comp1 ℓ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) = comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) →
    ∃ ε : Pt k 1 d, IsInvPair ε ℓ ∧ transF G.F ε ℓ = pt k (n := 2) d 0 + pt k (n := 2) d 1

theorem idMod2_of {d : ℕ} (ℓ : Pt k 1 d) (h0 : ∀ i, constantCoeff (ℓ i) = 0) (h1 : dLin ℓ = 1) :
    Formalism.FG.IsIdMod2 (fun p : Fin 1 × Fin d => ℓ p.2) := by
  refine ⟨fun p => h0 p.2, fun j i => ?_⟩
  obtain ⟨j1, j2⟩ := j
  obtain ⟨i1, i2⟩ := i
  have hj : j1 = 0 := Subsingleton.elim _ _
  have hi : i1 = 0 := Subsingleton.elim _ _
  subst hj hi
  have := congrFun (congrFun h1 j2) i2
  simp only [dLin, Matrix.one_apply] at this
  simp only [this, Prod.mk.injEq, true_and]
  by_cases h : i2 = j2
  · simp [h]
  · simp [h, Ne.symm h]

theorem subst_single_point_family {d : ℕ} {τ : Type} (ε : Fin d → MvPowerSeries τ k) :
    (fun p : Fin 1 × Fin d => (![ε] : Fin 1 → Fin d → MvPowerSeries τ k) p.1 p.2) = fun p => ε p.2 := by
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  rfl

theorem cc_ev {n m d : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j i, constantCoeff (a j i) = 0) {f : PS k m d}
    (hf : constantCoeff f = 0) : constantCoeff (ev a f) = 0 := by
  unfold ev
  exact constantCoeff_subst_eq_zero (hasSubst_pts a ha) (fun p => ha p.1 p.2) hf

theorem cc_pt {n d : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt k d j i) = 0 := by simp [pt]

theorem cc_comp1 {n d : ℕ} (φ : Pt k 1 d) (a : Pt k n d) (hφ : ∀ i, constantCoeff (φ i) = 0)
    (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin d) : constantCoeff (comp1 φ a i) = 0 :=
  cc_ev _ (fun j i => by fin_cases j; exact ha i) (hφ i)

theorem germComp1_germComp1_eq_substitute {n d : ℕ} (φ ψ : Pt k 1 d) (a : Pt k n d) (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (ha : ∀ i, constantCoeff (a i) = 0) : comp1 φ (comp1 ψ a) = comp1 (comp1 φ ψ) a := by
  funext i
  unfold comp1
  rw [ev_ev (![ψ] : Fin 1 → Pt k 1 d) (![a] : Fin 1 → Pt k n d) (fun j i => by fin_cases j; exact hψ i)
    (fun j i => by fin_cases j; exact ha i)]
  congr 1
  funext j
  fin_cases j
  rfl

theorem germCompOne_identityPoint_left {n d : ℕ} (a : Pt k n d) (ha : ∀ i, constantCoeff (a i) = 0) : comp1 (pt k d 0) a = a := by
  funext i
  unfold comp1
  exact ev_X (![a] : Fin 1 → Pt k n d) (fun j i => by fin_cases j; exact ha i) 0 i

theorem formal_exp_law : ExpLawSt := by
  intro k _ _ d G ℓ h0 h1 hadd
  have hid := idMod2_of ℓ h0 h1
  obtain ⟨h, hh0, hh⟩ := Formalism.FG.solve_exists_vector k (Fin 1 × Fin d) (Fin 1 × Fin d) (fun p => ℓ p.2) X hid
    (fun j => by simp)
  let ε : Pt k 1 d := fun i => h (0, i)
  have hε0 : ∀ i, constantCoeff (ε i) = 0 := fun i => hh0 (0, i)
  have hhε : h = fun p => ε p.2 := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j
    rfl
  have hLε : comp1 ℓ ε = pt k d 0 := by
    funext i
    show ev ![ε] (ℓ i) = X (0, i)
    unfold ev
    rw [subst_single_point_family, ← hhε]
    exact hh (0, i)
  have hsL : HasSubst (fun p : Fin 1 × Fin d => ℓ p.2) := hasSubst_of_constantCoeff_zero fun p => h0 p.2
  have hsh : HasSubst h := hasSubst_of_constantCoeff_zero hh0
  have hinj := Formalism.FG.subst_injective_vector k (Fin 1 × Fin d) (Fin 1 × Fin d) (fun p => ℓ p.2)
    (fun p => subst (fun q : Fin 1 × Fin d => ℓ q.2) (h p)) X hid
    (fun p => constantCoeff_subst_eq_zero hsL (fun q => h0 q.2) (hh0 p)) (fun p => by simp) (fun j => by
      rw [← subst_comp_subst_apply hsh hsL, hh j, subst_X hsL, subst_self]
      rfl)
  have hεL : comp1 ε ℓ = pt k d 0 := by
    funext i
    show ev ![ℓ] (ε i) = X (0, i)
    unfold ev
    rw [subst_single_point_family]
    exact congrFun hinj (0, i)
  refine ⟨ε, ⟨hε0, h0, hεL, hLε⟩, ?_⟩
  funext i
  have e : ev (n := 2) ![G.add (pt k d 0) (pt k d 1)] (ℓ i) =
      ev (n := 2) ![pt k d 0] (ℓ i) + ev (n := 2) ![pt k d 1] (ℓ i) := congrFun hadd i
  let b : Fin 2 → Pt k 2 d := ![comp1 ε (pt k d 0), comp1 ε (pt k d 1)]
  have hb : ∀ j i, constantCoeff (b j i) = 0 := by
    intro j i
    fin_cases j
    · exact cc_comp1 ε _ hε0 (cc_pt 0) i
    · exact cc_comp1 ε _ hε0 (cc_pt 1) i
  have hadd0 : ∀ j i, constantCoeff ((![G.add (pt k d 0) (pt k d 1)] : Fin 1 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact cc_ev _ (fun j i => by fin_cases j <;> exact cc_pt _ i) (G.const i)
  have hp0 : ∀ (l : Fin 2) j i, constantCoeff ((![pt k d l] : Fin 1 → Pt k 2 d) j i) = 0 := by
    intro l j i
    fin_cases j
    exact cc_pt l i
  have e2 := congrArg (ev b) e
  rw [ev_ev _ _ hadd0 hb, ev_add' _ hb, ev_ev _ _ (hp0 0) hb, ev_ev _ _ (hp0 1) hb] at e2
  have L1 : (fun (j : Fin 1) (m : Fin d) => ev b ((![G.add (pt k d 0) (pt k d 1)] : Fin 1 → Pt k 2 d) j m)) =
      ![addOf G.F (comp1 ε (pt k d 0)) (comp1 ε (pt k d 1))] := by
    funext j m
    fin_cases j
    show ev b (ev ![pt k d 0, pt k d 1] (G.F m)) = ev b (G.F m)
    rw [ev_ev _ _ (fun j i => by fin_cases j <;> exact cc_pt _ i) hb]
    congr 1
    funext j' m'
    fin_cases j' <;> exact ev_X b hb _ m'
  have L2 : ∀ l : Fin 2, (fun (j : Fin 1) (m : Fin d) => ev b ((![pt k d l] : Fin 1 → Pt k 2 d) j m)) =
      ![comp1 ε (pt k d l)] := by
    intro l
    funext j m
    fin_cases j
    fin_cases l <;> exact ev_X b hb _ m
  have L3 : ∀ l : Fin 2, ev (n := 2) ![comp1 ε (pt k d l)] (ℓ i) = pt k d l i := by
    intro l
    have := congrFun (germComp1_germComp1_eq_substitute ℓ ε (pt k (n := 2) d l) hε0 (cc_pt l)) i
    rw [hLε, germCompOne_identityPoint_left _ (cc_pt l)] at this
    exact this
  rw [L1, L2 0, L2 1, L3 0, L3 1] at e2
  exact e2


open Formalism.FG.SolveVAux in
theorem dLin_comp1 {d : ℕ} (φ ψ : Pt k 1 d) (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    dLin (comp1 φ ψ) = dLin φ * dLin ψ := by
  classical
  refine Matrix.ext fun i j => ?_
  simp only [dLin, Matrix.mul_apply]
  show coeff (Finsupp.single ((0 : Fin 1), j) 1) (ev ![ψ] (φ i)) = _
  unfold ev
  rw [subst_single_point_family]
  have hs : HasSubst (fun p : Fin 1 × Fin d => ψ p.2) := hasSubst_of_constantCoeff_zero fun p => hψ p.2
  have hlow : ∀ p : Fin 1 × Fin d, Formalism.FG.SolveVAux.Low 1 (ψ p.2) :=
    fun p => (Formalism.FG.SolveVAux.low_one_iff _).2 (hψ p.2)
  rw [coeff_subst hs, finsum_eq_sum_of_support_subset _
    (s := Finset.univ.image (fun p : Fin 1 × Fin d => Finsupp.single p 1))]
  · rw [Finset.sum_image (fun p _ q _ h => Finsupp.single_left_injective one_ne_zero h), Fintype.sum_prod_type,
      Fin.sum_univ_one]
    refine Finset.sum_congr rfl fun j' _ => ?_
    dsimp only
    rw [Finsupp.prod_single_index (h := fun (s : Fin 1 × Fin d) (e : ℕ) => ψ s.2 ^ e) (pow_zero _), pow_one,
      smul_eq_mul]
  · intro e he
    rw [Function.mem_support] at he
    by_contra hne
    apply he
    have hz : coeff (Finsupp.single ((0 : Fin 1), j) 1) (e.prod fun s n => (fun p : Fin 1 × Fin d => ψ p.2) s ^ n) =
        0 := by
      rcases Nat.lt_or_ge e.degree 2 with hd | hd
      · rcases Nat.lt_or_ge e.degree 1 with hd1 | hd1
        · have he0 : e = 0 := by
            have : e.degree = 0 := by omega
            exact (Finsupp.degree_eq_zero_iff e).1 this
          rw [he0, Finsupp.prod_zero_index, coeff_one, if_neg]
          exact Finsupp.single_ne_zero.2 one_ne_zero
        · obtain ⟨p, rfl⟩ := Formalism.FG.SolveVAux.degree_eq_one e (by omega)
          exact absurd (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ p))) hne
      · have hl := Formalism.FG.SolveVAux.low_P hlow e
        exact hl _ (by rw [Finsupp.degree_single]; omega)
    rw [hz, smul_zero]

theorem composition_identity_point_right {d : ℕ} (φ : Pt k 1 d) : comp1 φ (pt k d 0) = φ := by
  funext i
  unfold comp1
  have := ev_pt (k := k) (n := 1) (d := d) (φ i)
  convert this using 2
  funext j
  fin_cases j
  rfl

theorem add_at {d : ℕ} (G : FGLaw k d) (ℓ : Pt k 1 d)
    (hadd : comp1 ℓ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1))
    {n : ℕ} (u v : Pt k n d) (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    comp1 ℓ (addOf G.F u v) = comp1 ℓ u + comp1 ℓ v := by
  funext i
  have e : ev (n := 2) ![G.add (pt k d 0) (pt k d 1)] (ℓ i) =
      ev (n := 2) ![pt k d 0] (ℓ i) + ev (n := 2) ![pt k d 1] (ℓ i) := congrFun hadd i
  let b : Fin 2 → Pt k n d := ![u, v]
  have hb : ∀ j i, constantCoeff (b j i) = 0 := by
    intro j i
    fin_cases j
    · exact hu i
    · exact hv i
  have hadd0 : ∀ j i, constantCoeff ((![G.add (pt k d 0) (pt k d 1)] : Fin 1 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact cc_ev _ (fun j i => by fin_cases j <;> exact cc_pt _ i) (G.const i)
  have hp0 : ∀ (l : Fin 2) j i, constantCoeff ((![pt k d l] : Fin 1 → Pt k 2 d) j i) = 0 := by
    intro l j i
    fin_cases j
    exact cc_pt l i
  have e2 := congrArg (ev b) e
  rw [ev_ev _ _ hadd0 hb, ev_add' _ hb, ev_ev _ _ (hp0 0) hb, ev_ev _ _ (hp0 1) hb] at e2
  have L1 : (fun (j : Fin 1) (m : Fin d) => ev b ((![G.add (pt k d 0) (pt k d 1)] : Fin 1 → Pt k 2 d) j m)) =
      ![addOf G.F u v] := by
    funext j m
    fin_cases j
    show ev b (ev ![pt k d 0, pt k d 1] (G.F m)) = ev b (G.F m)
    rw [ev_ev _ _ (fun j i => by fin_cases j <;> exact cc_pt _ i) hb]
    congr 1
    funext j' m'
    fin_cases j' <;> exact ev_X b hb _ m'
  have L2 : (fun (j : Fin 1) (m : Fin d) => ev b ((![pt k d 0] : Fin 1 → Pt k 2 d) j m)) = ![u] := by
    funext j m
    fin_cases j
    exact ev_X b hb 0 m
  have L3 : (fun (j : Fin 1) (m : Fin d) => ev b ((![pt k d 1] : Fin 1 → Pt k 2 d) j m)) = ![v] := by
    funext j m
    fin_cases j
    exact ev_X b hb 1 m
  rw [L1, L2, L3] at e2
  exact e2


end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.FoldrIterateDerivationEq
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {d : ℕ}

section Mon
variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)

end Mon

section abelian₂
variable {ι : Type} [Fintype ι] [DecidableEq ι] (ψ : List ι → k)

def lamW (P : MvPolynomial ι k) : k :=
  (AddMonoidAlgebra.coeff P).sum (fun n a => a * ψ (word (Finset.univ : Finset ι).toList n))

theorem lamW_add (P Q : MvPolynomial ι k) : lamW ψ (P + Q) = lamW ψ P + lamW ψ Q := by
  show (AddMonoidAlgebra.coeff P + AddMonoidAlgebra.coeff Q).sum _ = _
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem lamW_monomial (n : ι →₀ ℕ) (a : k) :
    lamW ψ (MvPolynomial.monomial n a) = a * ψ (word (Finset.univ : Finset ι).toList n) := by
  show (Finsupp.single n a).sum _ = _
  exact Finsupp.sum_single_index (zero_mul _)

theorem lamW_sum (s : Finset ι) (f : ι → MvPolynomial ι k) :
    lamW ψ (∑ i ∈ s, f i) = ∑ i ∈ s, lamW ψ (f i) := by
  let L : MvPolynomial ι k →+ k :=
    { toFun := lamW ψ, map_zero' := by simpa using lamW_add ψ 0 0, map_add' := lamW_add ψ }
  exact map_sum L f s

def rW (c : ι → ι → k) (n : ι →₀ ℕ) : k :=
  ((Finset.univ : Finset ι).toList.map (fun x => ((Finset.univ : Finset ι).toList.map (fun y =>
    c x y * ((n y * (n - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k) *
      ψ (word (Finset.univ : Finset ι).toList (n - Finsupp.single y 1 - Finsupp.single x 1)))).sum)).sum

theorem secondOrder_add (c : ι → ι → k) (p q : MvPolynomial ι k) :
    secondOrder k c (p + q) = secondOrder k c p + secondOrder k c q := by
  unfold secondOrder
  simp only [map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]
  done

theorem lamW_secondOrder (c : ι → ι → k) (P : MvPolynomial ι k) :
    lamW ψ (secondOrder k c P) = (AddMonoidAlgebra.coeff P).sum (fun n a => a * rW ψ c n) := by
  refine MvPolynomial.induction_on' P (fun n a => ?_) (fun p q hp hq => ?_)
  · show lamW ψ (secondOrder k c (MvPolynomial.monomial n a)) =
      (Finsupp.single n a).sum fun m b => b * rW ψ c m
    have hL : ∀ g : ι → k, ((Finset.univ : Finset ι).toList.map g).sum = ∑ i, g i := by
      intro g
      first
        | exact Finset.sum_map_toList _ _
        | exact Finset.sum_toList _ _
        | rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList, Multiset.map_coe, Multiset.sum_coe]
    rw [Finsupp.sum_single_index (zero_mul _)]
    simp only [secondOrder, lamW_sum, MvPolynomial.pderiv_monomial, MvPolynomial.C_mul_monomial,
      lamW_monomial, rW, hL, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [Nat.cast_mul]
    ring
  · rw [secondOrder_add, lamW_add, hp, hq]
    show _ = (AddMonoidAlgebra.coeff p + AddMonoidAlgebra.coeff q).sum _
    rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]

end abelian₂

end ReciprocityTheory.ChartRestriction.G.TB.G2
end
end

