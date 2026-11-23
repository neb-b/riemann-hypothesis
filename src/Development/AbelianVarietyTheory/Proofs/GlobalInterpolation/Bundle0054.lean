module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0050
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.QNormal

open Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K]

def IntV (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (v : Fin N → E) : Prop := ∀ l, IntAt P (v l)

def IntHom (P : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (y : (Fin a → E) →ₗ[E] (Fin b → E)) : Prop :=
  ∀ v, IntV P v → IntV P (y v)

def HomBdd (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) {a b : ℕ} (Psi : Loc.SF E K a b) : Prop :=
  (∀ x, Psi x ≠ 0 → IntHom P (((qOf P : E) ^ N) • x)) ∧
    ∀ x y, IntHom P y → Psi (x + ((qOf P : E) ^ N) • y) = Psi x

def FunBdd (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) {ι : Type} (f : (ι → E) → K) : Prop :=
  (∀ t, f t ≠ 0 → ∀ i, IntAt P ((qOf P : E) ^ N * t i)) ∧
    ∀ t u : ι → E, (∀ i, IntAt P (u i)) → f (t + ((qOf P : E) ^ N) • u) = f t

def CharTo (P : HeightOneSpectrum (𝓞 E)) (D : ℕ) (psi : E → K) : Prop :=
  (∀ x y : E, IntAt P ((qOf P : E) ^ D * x) → IntAt P ((qOf P : E) ^ D * y) → psi (x + y) = psi x * psi y) ∧
    ∀ x : E, IntAt P x → psi x = 1

def boxSum (P : HeightOneSpectrum (𝓞 E)) (A B : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) : K :=
  (((qOf P : K) ^ B)⁻¹) ^ Fintype.card ι * ∑ t ∈ Fintype.piFinset fun _ : ι => LocE.valsQ E (qOf P) A B, f t

def integrand (psi : E → K) {n' c' n c : ℕ} (Psi : Loc.SF E K (n' + c') (n + c)) (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t : Loc.FC n' c' n c → E) : K :=
  Psi (Loc.xx1 xj t) * psi (-Loc.chArg (Loc.xx1 xj t))

def UnfNe (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) {n' c' n c : ℕ} (Psi : Loc.SF E K (n' + c') (n + c)) : Prop :=
  ∃ A₀ B₀ : ℕ, ∀ A B, A₀ ≤ A → B₀ ≤ B → IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB P psi A B Psi ≠ 0

theorem IntV.zero (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} : IntV P (0 : Fin N → E) := fun _ => IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem IntV.add {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} {v w : Fin N → E} (hv : IntV P v) (hw : IntV P w) : IntV P (v + w) :=
  fun l => (hv l).add (hw l)

theorem IntV.neg {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} {v : Fin N → E} (hv : IntV P v) : IntV P (-v) :=
  fun l => IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (hv l)

theorem IntV.smul {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} {u : E} {v : Fin N → E} (hu : IntAt P u) (hv : IntV P v) :
    IntV P (u • v) := fun l => hu.mul (hv l)

theorem intAt_one (P : HeightOneSpectrum (𝓞 E)) : IntAt P (1 : E) := by simpa using IntAt.coe P 1

theorem intAt_sum {P : HeightOneSpectrum (𝓞 E)} {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    IntAt P (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IntAt P) (fun _ _ => IntAt.add) (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P) h

theorem intV_single (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (s : Fin N) : IntV P (Pi.single s (1 : E) : Fin N → E) := by
  intro l
  rw [Pi.single_apply]
  split_ifs
  · exact intAt_one P
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem intHom_iff {P : HeightOneSpectrum (𝓞 E)} {a b : ℕ} (y : (Fin a → E) →ₗ[E] (Fin b → E)) :
    IntHom P y ↔ ∀ s l, IntAt P (y (Pi.single s 1) l) := by
  refine ⟨fun h s l => h _ (intV_single P s) l, fun h v hv l => ?_⟩
  have e : y v = ∑ s, v s • y (Pi.single s 1) := by
    conv_lhs => rw [show v = ∑ s, v s • (Pi.single s (1 : E) : Fin a → E) from by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [e, Finset.sum_apply]
  exact intAt_sum _ _ fun s _ => (hv s).mul (h s l)

theorem mem_stdAt_iff [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} (v : Fin N → E) : v ∈ stdAt E N P ↔ IntV P v :=
  mem_localization_standardLattice P v


section Flags

variable {F : Type} [Field F] {n c : ℕ}

theorem inX_apply (x : Fin n → F) (l : Fin (n + c)) : Loc.inX F n c x l = if h : l.1 < n then x ⟨l.1, h⟩ else 0 := by
  unfold Loc.inX
  rw [LinearMap.pi_apply]
  split_ifs <;> simp

theorem mem_Ufl {i : ℕ} {v : Fin (n + c) → F} : v ∈ Loc.Ufl F n c i ↔ ∀ l : Fin (n + c), ¬ l.1 < n + i → v l = 0 := Iff.rfl

theorem inX_mem_Ufl (i : ℕ) (x : Fin n → F) : Loc.inX F n c x ∈ Loc.Ufl F n c i :=
  mem_Ufl.2 fun l hl => by rw [inX_apply, dite_eq_right (by omega)]

theorem Ufl_mono {i j : ℕ} (h : i ≤ j) : Loc.Ufl F n c i ≤ Loc.Ufl F n c j :=
  fun _ hv => mem_Ufl.2 fun l hl => mem_Ufl.1 hv l (by omega)

theorem eN_mem_Ufl {i s : ℕ} (h : s < n + i) : Loc.eN F (n + c) s ∈ Loc.Ufl F n c i :=
  mem_Ufl.2 fun l hl => by
    unfold Loc.eN
    rw [if_neg (by omega)]

theorem inX_castAdd (x : Fin n → F) (a : Fin n) : Loc.inX F n c x (Fin.castAdd c a) = x a := by
  rw [inX_apply, dite_eq_left (by simp)]
  rfl

theorem inX_of_mem_Ufl {v : Fin (n + c) → F} (hv : v ∈ Loc.Ufl F n c 0) :
    Loc.inX F n c (fun a => v (Fin.castAdd c a)) = v := by
  funext l
  rw [inX_apply]
  split_ifs with h
  · rfl
  · exact (mem_Ufl.1 hv l (by omega)).symm

theorem inX_injective : Function.Injective (Loc.inX F n c) := fun x y h => by
  funext a
  rw [← inX_castAdd (c := c) x, h, inX_castAdd]

theorem exists_res {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)} (hr : r ∈ Loc.R1 F n c) :
    ∃ γ : (Fin n → F) ≃ₗ[F] (Fin n → F), ∀ x, r (Loc.inX F n c x) = Loc.inX F n c (γ x) := by
  have key : ∀ s : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F), Loc.R1cond F n c s → ∀ x,
      Loc.inX F n c ((LinearMap.funLeft F F (Fin.castAdd c) ∘ₗ s.toLinearMap ∘ₗ Loc.inX F n c) x) = s (Loc.inX F n c x) :=
    fun s hs x => inX_of_mem_Ufl (hs.1 0 _ (inX_mem_Ufl 0 x))
  refine ⟨LinearEquiv.ofLinear (LinearMap.funLeft F F (Fin.castAdd c) ∘ₗ r.toLinearMap ∘ₗ Loc.inX F n c)
    (LinearMap.funLeft F F (Fin.castAdd c) ∘ₗ (r⁻¹).toLinearMap ∘ₗ Loc.inX F n c) ?_ ?_, fun x => (key r hr.1 x).symm⟩
  · refine LinearMap.ext fun x => inX_injective (c := c) ?_
    rw [LinearMap.comp_apply, key r hr.1, key r⁻¹ hr.2]
    exact r.apply_symm_apply _
  · refine LinearMap.ext fun x => inX_injective (c := c) ?_
    rw [LinearMap.comp_apply, key r⁻¹ hr.2, key r hr.1]
    exact r.symm_apply_apply _

theorem atN_add {N : ℕ} (v w : Fin N → F) (i : ℕ) : Loc.atN (v + w) i = Loc.atN v i + Loc.atN w i := by
  unfold Loc.atN
  split_ifs <;> simp

theorem atN_sub {N : ℕ} (v w : Fin N → F) (i : ℕ) : Loc.atN (v - w) i = Loc.atN v i - Loc.atN w i := by
  unfold Loc.atN
  split_ifs <;> simp

theorem atN_smul {N : ℕ} (a : F) (v : Fin N → F) (i : ℕ) : Loc.atN (a • v) i = a * Loc.atN v i := by
  unfold Loc.atN
  split_ifs <;> simp

theorem atN_of_mem_Ufl {i : ℕ} {v : Fin (n + c) → F} (hv : v ∈ Loc.Ufl F n c i) : Loc.atN v (n + i) = 0 := by
  unfold Loc.atN
  split_ifs with h
  · exact mem_Ufl.1 hv _ (by simp)
  · rfl

theorem atN_of_R1cond {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)} (hr : Loc.R1cond F n c r) {i : ℕ}
    {v : Fin (n + c) → F} (hv : v ∈ Loc.Ufl F n c (i + 1)) : Loc.atN (r v) (n + i) = Loc.atN v (n + i) := by
  have h1 : v - Loc.atN v (n + i) • Loc.eN F (n + c) (n + i) ∈ Loc.Ufl F n c i := mem_Ufl.2 fun l hl => by
    simp only [Pi.sub_apply, Pi.smul_apply, Loc.eN, smul_eq_mul]
    split_ifs with h
    · unfold Loc.atN
      rw [dite_eq_left (h ▸ l.2), mul_one, sub_eq_zero]
      congr 1
      exact Fin.ext h
    · rw [mem_Ufl.1 hv l (by omega)]
      simp
  have h2 := atN_of_mem_Ufl (hr.1 i _ h1)
  have h3 := atN_of_mem_Ufl (hr.2.2 i)
  have h4 := atN_of_mem_Ufl h1
  rw [map_sub, map_smul, atN_sub, atN_smul] at h2
  rw [atN_sub] at h3
  rw [atN_sub, atN_smul] at h4
  linear_combination h2 - h4 + Loc.atN v (n + i) * h3

theorem unipotentCharacterArgument_mul_stabilizer {r s : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)} (hr : Loc.R1cond F n c r) (hs : Loc.R1cond F n c s) :
    Loc.n1Arg (r * s) = Loc.n1Arg r + Loc.n1Arg s := by
  unfold Loc.n1Arg
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := atN_of_R1cond hr (hs.2.2 (i + 1))
  have h2 : Loc.atN (Loc.eN F (n + c) (n + (i + 1))) (n + i) = 0 := by
    unfold Loc.atN Loc.eN
    split_ifs with h h'
    · simp at h'
    · rfl
    · rfl
  rw [map_sub, atN_sub, atN_sub, h2] at h1
  change Loc.atN (r (s (Loc.eN F (n + c) (n + (i + 1))))) (n + i) =
    Loc.atN (r (Loc.eN F (n + c) (n + (i + 1)))) (n + i) + Loc.atN (s (Loc.eN F (n + c) (n + (i + 1)))) (n + i)
  linear_combination h1

theorem linearMap_unfolding_apply_single {n' c' : ℕ} (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F) (s : Fin (n' + c'))
    (l : Fin (n + c)) : Loc.xx1 xj t (Pi.single s 1) l =
      if hf : Loc.IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
      else if hs : s.1 < n' then (if hl : l.1 < n then xj (Pi.single ⟨s.1, hs⟩ 1) ⟨l.1, hl⟩ else 0)
      else if l.1 = n + (s.1 - n') then 1 else 0 := by
  unfold Loc.xx1
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  simp only [Matrix.col_apply, Matrix.of_apply, LinearMap.toMatrix'_apply]

theorem unfoldingAffinePointMap_apply_inclusion {n' c' : ℕ} (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F) (v : Fin n' → F) :
    Loc.xx1 xj t (Loc.inX F n' c' v) = Loc.inX F n c (xj v) := by
  have : Loc.xx1 xj t ∘ₗ Loc.inX F n' c' = Loc.inX F n c ∘ₗ xj := by
    refine LinearMap.pi_ext' fun a => LinearMap.ext_ring ?_
    have e : Loc.inX F n' c' (Pi.single a 1) = Pi.single (Fin.castAdd c' a) 1 := by
      funext l
      rw [inX_apply, Pi.single_apply]
      split_ifs with h1 h2 h2
      · subst h2
        simp
      · rw [Pi.single_apply, if_neg]
        rintro rfl
        exact h2 rfl
      · subst h2
        simp at h1
      · rfl
    funext l
    change Loc.xx1 xj t (Loc.inX F n' c' (Pi.single a 1)) l = Loc.inX F n c (xj (Pi.single a 1)) l
    rw [e, linearMap_unfolding_apply_single, dite_eq_right (fun h => by have := h.1; have := a.2; simp at *; omega), dite_eq_left (by simp), inX_apply]
    rfl
  exact LinearMap.congr_fun this v

end Flags

end GlobalTheory.QNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedLeadingTermSplitZMinor
section
open MvPolynomial NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance GlobalTheory.BranchFormula

noncomputable section

namespace GlobalTheory.XiTopCoef

section Top

variable {σ A : Type} [CommRing A] (w : σ → ℕ)

def TopTerm (f : MvPolynomial σ A) (d : σ →₀ ℕ) (c : A) : Prop :=
  AddMonoidAlgebra.coeff f d = c ∧ ∀ m ∈ f.support, m = d ∨ Finsupp.weight w m < Finsupp.weight w d

variable {w}

theorem TopTerm.C (c : A) : TopTerm w (C c : MvPolynomial σ A) 0 c := by
  classical
  refine ⟨by simp, fun m hm => Or.inl ?_⟩
  by_contra h
  rw [mem_support_iff, coeff_C, if_neg (Ne.symm h)] at hm
  exact hm rfl

theorem TopTerm.mul {f g : MvPolynomial σ A} {d e : σ →₀ ℕ} {c c' : A} (hf : TopTerm w f d c) (hg : TopTerm w g e c') :
    TopTerm w (f * g) (d + e) (c * c') := by
  classical
  constructor
  · rw [coeff_mul, Finset.sum_eq_single (d, e), hf.1, hg.1]
    · rintro ⟨x, y⟩ hxy hne
      by_contra h0
      have hx := hf.2 x (mem_support_iff.2 (left_ne_zero_of_mul h0))
      have hy := hg.2 y (mem_support_iff.2 (right_ne_zero_of_mul h0))
      have hs : x + y = d + e := by simpa using hxy
      have hw := congrArg (Finsupp.weight w) hs
      rw [map_add (f := _), map_add (f := _)] at hw
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact hne rfl
      all_goals omega
    · intro h
      exact absurd (by simp) h
  · intro m hm
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (support_mul f g hm)
    rw [map_add (f := _), map_add (f := _)]
    rcases hf.2 x hx with rfl | hx <;> rcases hg.2 y hy with rfl | hy
    · exact Or.inl rfl
    all_goals right; omega

theorem TopTerm.pow {f : MvPolynomial σ A} {d : σ →₀ ℕ} {c : A} (hf : TopTerm w f d c) (k : ℕ) :
    TopTerm w (f ^ k) (k • d) (c ^ k) := by
  induction k with
  | zero => simpa using TopTerm.C (w := w) (1 : A)
  | succ k ih => rw [pow_succ, pow_succ, succ_nsmul]; exact ih.mul hf

theorem TopTerm.prod {ι : Type} (s : Finset ι) {f : ι → MvPolynomial σ A} {d : ι → σ →₀ ℕ} {c : ι → A}
    (h : ∀ i, TopTerm w (f i) (d i) (c i)) : TopTerm w (∏ i ∈ s, f i) (∑ i ∈ s, d i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using TopTerm.C (w := w) (1 : A)
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]; exact (h a).mul ih

theorem TopTerm.linear {k : ℕ} (v : Fin (k + 1) → σ) (c : Fin (k + 1) → A)
    (hv : ∀ q : Fin k, w (v q.castSucc) < w (v (Fin.last k))) :
    TopTerm w (∑ q, X (v q) * MvPolynomial.C (c q)) (Finsupp.single (v (Fin.last k)) 1) (c (Fin.last k)) := by
  classical
  have e : ∀ q, (X (v q) * MvPolynomial.C (c q) : MvPolynomial σ A) = monomial (Finsupp.single (v q) 1) (c q) := by
    intro q
    rw [mul_comm, C_mul_X_eq_monomial]
  simp only [e]
  constructor
  · rw [coeff_sum, Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add, coeff_monomial, if_pos rfl]
    intro q _
    rw [coeff_monomial, if_neg]
    intro h
    have h1 := Finsupp.single_left_injective one_ne_zero h
    have := hv q
    rw [h1] at this
    exact lt_irrefl _ this
  · intro m hm
    obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.1 (support_sum hm)
    have hq' := Finset.mem_singleton.1 (support_monomial_subset hq)
    subst hq'
    induction q using Fin.lastCases with
    | last => exact Or.inl rfl
    | cast q => right; simpa [Finsupp.weight_single] using hv q

end Top

variable (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1)

def lp (n k : ℕ) : Pol K Unit n :=
  if h : k ≤ n then rename (fun v : Fin n × Fin n => (((), v) : Unit × Fin n × Fin n)) (Formalism.GradedWeylDivisibility.lpMinor K k h h) else 1

theorem lp_eq {k : ℕ} (h : k ≤ n) :
    lp K n k = (Matrix.of fun p q : Fin k => (X ((), Fin.castLE h p, Fin.castLE h q) : Pol K Unit n)).det := by
  rw [lp, dif_pos h, Formalism.GradedWeylDivisibility.lpMinor, AlgHom.map_det]
  congr 1
  ext p q
  simp

theorem lp_zero : lp K n 0 = 1 := by
  rw [lp_eq K (Nat.zero_le n), Matrix.det_isEmpty]

theorem split_lp {k : ℕ} (h : k ≤ n) (h' h'' : k ≤ N) :
    splitLast K Unit hN (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) (Formalism.GradedWeylDivisibility.lpMinor K k h' h'')) =
      C (lp K n k) := by
  rw [lp_eq K h, Formalism.GradedWeylDivisibility.lpMinor, AlgHom.map_det, AlgHom.map_det, RingHom.map_det]
  congr 1
  ext1 p q
  simp only [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X]
  exact splitLast_X_up K Unit hN () (Fin.castLE h p) (Fin.castLE h q)

theorem weightedLeadingTerm_split_zMinor (i : Fin n) :
    TopTerm (fun p : Unit × Fin n => p.2.val)
      (splitLast K Unit hN (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) (Br.zMinor K hN i)))
      (Finsupp.single ((), i) 1) (lp K n i) := by
  have hi : i.val + 1 ≤ n := i.2
  have hi' : i.val ≤ n := i.2.le
  have key := TopTerm.linear (w := fun p : Unit × Fin n => p.2.val) (k := i.val) (fun q => ((), Fin.castLE hi q))
    (fun q => (-1) ^ (i.val + q.val) * (Matrix.of fun p r : Fin i.val =>
      (X ((), Fin.castLE hi' p, Fin.castLE hi (q.succAbove r)) : Pol K Unit n)).det) (fun q => by simp)
  convert key using 1
  · rw [Br.zMinor, Formalism.GradedWeylDivisibility.initMinor, AlgHom.map_det, AlgHom.map_det, Matrix.det_succ_row _ (Fin.last i.val)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, RingHom.map_det, map_pow, map_neg, map_one, mul_left_comm, ← mul_assoc]
    congr 2
    · simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X, Fin.val_last, lt_irrefl, dif_neg,
        not_false_eq_true]
      exact splitLast_X_lastRow K Unit hN () (Fin.castLE hi q)
    · ext1 p r
      simp only [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X,
        Matrix.submatrix_apply, Fin.succAbove_last, Fin.val_castSucc, p.2, dif_pos]
      exact splitLast_X_up K Unit hN () (Fin.castLE hi' p) (Fin.castLE hi (q.succAbove r))
  · rfl
  · rw [lp_eq K hi', Fin.val_last, ← two_mul, pow_mul]
    simp only [Fin.succAbove_last, even_two, Even.neg_pow, one_pow, one_mul]
    rfl

theorem prod_shift {M : Type} [CommMonoid M] (P : ℕ → M) (h0 : P 0 = 1) (b : Fin n → ℕ) :
    ∏ i : Fin n, P i ^ b i = ∏ i : Fin n, P (i + 1) ^ Formalism.GradedWeylDivisibility.nuNext b i := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
    simp [h0, Formalism.GradedWeylDivisibility.nuNext]
    rfl

theorem exp_eq (lam : DomWeight N) (sg : DomWeight n) (hI : Br.Interlace hN lam sg) (hS : Br.SameShift lam sg) (i : Fin n) :
    (Br.aBr hN lam sg i).toNat + Formalism.GradedWeylDivisibility.nuNext (fun s => (Br.bBr hN lam sg s).toNat) i =
      sg.natW i - Formalism.GradedWeylDivisibility.nuNext sg.natW i := by
  subst hN
  have hn : 0 < n := i.pos
  have h1 := (hI i).1
  have e1 : sg.detShift = sg.w ⟨n - 1, by omega⟩ := dif_pos hn
  have e2 : lam.detShift = lam.w ⟨n, by omega⟩ := dif_pos (Nat.succ_pos n)
  unfold Br.SameShift at hS
  unfold Formalism.GradedWeylDivisibility.nuNext
  split_ifs with h
  · have h2 := (hI ⟨i.val + 1, h⟩).2
    have h3 : sg.w ⟨n - 1, by omega⟩ ≤ sg.w ⟨i.val + 1, h⟩ := sg.anti (by simp only [Fin.le_def]; omega)
    simp only [Br.aBr, Br.bBr, Br.iS, Br.iC, DomWeight.natW] at *
    omega
  · have hi : i = ⟨n - 1, by omega⟩ := Fin.ext (by have := i.2; simp only; omega)
    have e3 : lam.w (Br.iS rfl i) = lam.w ⟨n, by omega⟩ := by
      congr 1
      exact Fin.ext (by have := i.2; simp only [Br.iS]; omega)
    rw [← hi] at e1
    simp only [Br.aBr, DomWeight.natW] at *
    omega

theorem coefLast_xi : ∀ (K : Type) [Field K] (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n), Br.Interlace hN lam sg → Br.SameShift lam sg → Br.coefLast (K := K) hN (Br.bExp hN (fun _ : Unit => lam) (fun _ : Unit => sg)) (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N)) (Br.xiBr K hN lam sg)) = rename (fun v : Fin n × Fin n => (((), v) : Unit × Fin n × Fin n)) (extremal K n sg) := by
  intro K _ N n hN lam sg hI hS
  have key := (TopTerm.prod (w := fun p : Unit × Fin n => p.2.val) Finset.univ fun i : Fin n =>
    ((TopTerm.C (lp K n (i.val + 1))).pow (Br.aBr hN lam sg i).toNat).mul
      ((weightedLeadingTerm_split_zMinor K hN i).pow (Br.bBr hN lam sg i).toNat)).1
  rw [coefLast_eq_coeff, Br.xiBr, map_prod, map_prod]
  simp only [map_mul, map_pow]
  have hsp : ∀ i : Fin n, _ := fun i : Fin n =>
    split_lp K hN (k := i.val + 1) i.2 (by have := i.2; omega) (by have := i.2; omega)
  simp only [hsp]
  refine Eq.trans (congrArg (fun e => AddMonoidAlgebra.coeff _ e) ?_) (key.trans ?_)
  · ext ⟨u, s⟩
    simp [Br.bExp, Finsupp.finsetSum_apply, Finsupp.single_apply]
  · rw [Finset.prod_mul_distrib, prod_shift (lp K n) (lp_zero K) fun s => (Br.bBr hN lam sg s).toNat,
      ← Finset.prod_mul_distrib, extremal, Formalism.GradedWeylDivisibility.hw, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add, exp_eq hN lam sg hI hS, map_pow, lp, dif_pos (show i.val + 1 ≤ n from i.2)]

end GlobalTheory.XiTopCoef
end
end

