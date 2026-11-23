module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0003

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FiniteRestrictSupport
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem finite_restrictSupport' (R : Type) [CommRing R] (σ : Type) (s : Set (σ →₀ ℕ)) (hs : s.Finite) :
    (restrictSupport R s : Submodule R (MvPolynomial σ R)).FG := by
  have heq : (restrictSupport R s : Submodule R (MvPolynomial σ R)) =
      Submodule.span R ((fun m => (monomial m (1 : R) : MvPolynomial σ R)) '' s) := by
    apply le_antisymm
    · intro P hP
      rw [MvPolynomial.mem_restrictSupport_iff] at hP
      rw [P.as_sum]
      refine Submodule.sum_mem _ fun m hm => ?_
      have : (monomial m (AddMonoidAlgebra.coeff P m) : MvPolynomial σ R) = AddMonoidAlgebra.coeff P m • monomial m (1 : R) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hP (by exact_mod_cast hm), rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      rw [SetLike.mem_coe, MvPolynomial.mem_restrictSupport_iff]
      intro m' hm'
      have := MvPolynomial.support_monomial_subset (by exact_mod_cast hm')
      rw [Finset.mem_singleton] at this
      rw [this]; exact hm
  rw [heq]
  exact Submodule.fg_span (hs.image _)

theorem segDegSet_finite {r : ℕ} (K : ℕ) (b : ℤ → ℕ) (L : Finset ℤ) (hb : ∀ x, x ∉ L → b x = 0) :
    (Dat.segDegSet (r := r) K b).Finite := by
  classical
  let B : ℤ × Fin (r + K) →₀ ℕ := Finsupp.onFinset (L ×ˢ Finset.univ) (fun v => b v.1) (by
    intro v hv
    by_contra h
    apply hv
    apply hb
    intro hL
    exact h (Finset.mem_product.mpr ⟨hL, Finset.mem_univ _⟩))
  refine (Set.finite_Iic B).subset ?_
  intro m hm v
  have h := hm v.1
  have : m (v.1, v.2) ≤ ∑ c : Fin (r + K), m (v.1, c) :=
    Finset.single_le_sum (f := fun c => m (v.1, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)
  rw [h] at this
  simpa [B] using this

theorem restFin : RestFin := by
  intro p n' r K _ _ _ X O _ _ _ j b hb
  have hfg := finite_restrictSupport' O (ℤ × Fin (r + K)) _ (segDegSet_finite (r := r) K b (X.F.letters j) hb)
  have hN : IsNoetherian O (restrictSupport O (Dat.segDegSet (r := r) K b) : Submodule O (SegRing O r K)) :=
    isNoetherian_of_fg_of_noetherian _ hfg
  have hle : X.Mj p K O j b ≤ restrictSupport O (Dat.segDegSet (r := r) K b) := by
    intro P hP
    exact hP.1.2
  have : IsNoetherian O (X.Mj p K O j b) := isNoetherian_of_le hle
  infer_instance

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ScaleSCoeffZero
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

section Kill

variable {R σ : Type} [CommRing R] (S : Set σ)


open Classical in
def kill : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun v => if v ∈ S then 0 else MvPolynomial.X v


open Classical in
def scaleS : MvPolynomial σ R →ₐ[R] Polynomial (MvPolynomial σ R) :=
  aeval fun v => if v ∈ S then Polynomial.X * Polynomial.C (MvPolynomial.X v) else Polynomial.C (MvPolynomial.X v)


open Classical in
def offDeg : (σ →₀ ℕ) →+ ℕ := Finsupp.liftAddHom fun v => if v ∈ S then AddMonoidHom.id ℕ else 0

theorem scaleS_monomial (m : σ →₀ ℕ) :
    scaleS (R := R) S (monomial m 1) = Polynomial.C (monomial m 1) * Polynomial.X ^ offDeg S m := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    have : (monomial (f + g) (1 : R)) = monomial f 1 * monomial g 1 := by
      rw [monomial_mul, one_mul]
    rw [this, map_mul, hf, hg, map_add (f := _), pow_add, map_mul]
    ring
  | single v k =>
    rw [← MvPolynomial.X_pow_eq_monomial, map_pow]
    by_cases hv : v ∈ S
    · have h1 : scaleS (R := R) S (MvPolynomial.X v) = Polynomial.X * Polynomial.C (MvPolynomial.X v) := by
        simp [scaleS, hv]
      have h2 : offDeg S (Finsupp.single v k) = k := by simp [offDeg, hv]
      rw [h1, h2, mul_pow, Polynomial.C_pow, mul_comm]
    · have h1 : scaleS (R := R) S (MvPolynomial.X v) = Polynomial.C (MvPolynomial.X v) := by
        simp [scaleS, hv]
      have h2 : offDeg S (Finsupp.single v k) = 0 := by simp [offDeg, hv]
      rw [h1, h2, pow_zero, mul_one, Polynomial.C_pow]

theorem scaleS_coeff_zero (f : MvPolynomial σ R) : (scaleS S f).coeff 0 = kill S f := by
  classical
  have h : (Polynomial.constantCoeff.comp (scaleS (R := R) S : MvPolynomial σ R →+* Polynomial (MvPolynomial σ R))) =
      (kill (R := R) S : MvPolynomial σ R →+* MvPolynomial σ R) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [scaleS, kill, MvPolynomial.algebraMap_eq]
    · intro v
      by_cases hv : v ∈ S <;> simp [scaleS, kill, hv]
  have := congrArg (fun g => g f) h
  simpa [Polynomial.constantCoeff_apply] using this

theorem li_of_kill {ι : Type} (m : ι → σ →₀ ℕ) (w : ι → MvPolynomial σ R)
    (h : LinearIndependent R fun q => monomial (m q) (1 : R) * kill S (w q)) :
    LinearIndependent R fun q => monomial (m q) (1 : R) * w q := by
  classical
  rw [linearIndependent_iff'] at h ⊢
  intro s a hsum
  by_contra hne
  push Not at hne
  obtain ⟨q0, hq0s, hq0⟩ := hne
  let s' := s.filter fun q => a q ≠ 0
  have hs' : s'.Nonempty := ⟨q0, Finset.mem_filter.mpr ⟨hq0s, hq0⟩⟩
  obtain ⟨q1, hq1, hmin⟩ := Finset.exists_min_image s' (fun q => offDeg S (m q)) hs'
  set δ := offDeg S (m q1) with hδ
  have hsum' : ∑ q ∈ s', a q • (monomial (m q) (1 : R) * w q) = 0 := by
    rw [← hsum]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro q hq hq'
    have : a q = 0 := by
      by_contra hh
      exact hq' (Finset.mem_filter.mpr ⟨hq, hh⟩)
    rw [this, zero_smul]
  have hΘ := congrArg (fun P => (scaleS S P).coeff δ) hsum'
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, map_mul, scaleS_monomial, Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
    map_zero, Polynomial.coeff_zero] at hΘ
  have hterm : ∀ q ∈ s', (Polynomial.C (monomial (m q) (1 : R)) * Polynomial.X ^ offDeg S (m q) *
      scaleS S (w q)).coeff δ = if offDeg S (m q) = δ then monomial (m q) (1 : R) * kill S (w q) else 0 := by
    intro q hq
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    have hle := hmin q hq
    split_ifs with h1 h2 h2
    · rw [h2, Nat.sub_self, scaleS_coeff_zero]
    · exact absurd (le_antisymm h1 hle) h2
    · exact absurd (le_of_eq h2) h1
    · rw [mul_zero]
  rw [Finset.sum_congr rfl fun q hq => by rw [hterm q hq]] at hΘ
  have hΘ' : ∑ q ∈ s'.filter (fun q => offDeg S (m q) = δ), a q • (monomial (m q) (1 : R) * kill S (w q)) = 0 := by
    rw [Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) hΘ
    split_ifs <;> simp
  have := h _ a hΘ' q1 (Finset.mem_filter.mpr ⟨hq1, rfl⟩)
  exact (Finset.mem_filter.mp hq1).2 this

end Kill

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ)


omit [NeZero n'] in
def offSet (j : ℤ) : Set (ℤ × Fin (r + K)) :=
  {v | ∃ t c : Fin r, c ≠ Fin.rev t ∧ v = (X.F.fr j t.val, Fin.castAdd K c)}


omit [NeZero n'] in
def monTau (j : ℤ) (u : Fin r × Fin r → ℕ) : ℤ × Fin (r + K) →₀ ℕ :=
  ∑ v : Fin r × Fin r, Finsupp.single (X.F.fr j v.1.val, Fin.castAdd K v.2) (u v)

def wordEl (O : Type) [CommRing O] (j : ℤ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) : SegRing O r K :=
  segRen X.F j O (r + K) (PsiPl O (plPart q.1) (Ican (plPart q.1)) * PsiTan O (tanPart q.1) q.2.1)

end Dat

def RestKey (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b →
      LinearIndependent O fun q : X.Idx p K j (X.restr j b) =>
        monomial (X.monTau K j q.1.2.2) (1 : O) * kill (X.offSet K j) (X.wordEl K O j q.1)

theorem fr_injective {n' r : ℕ} [NeZero n'] (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) :
    Function.Injective fun a : Fin r => F.fr j a.val := by
  obtain ⟨-, -, h3, -⟩ := hV
  have key : ∀ d a : ℕ, a + d + 1 < r → F.fr j a < F.fr j (a + d + 1) := by
    intro d
    induction d with
    | zero => intro a h; exact h3 j a h
    | succ d ih => intro a h; exact lt_trans (ih a (by omega)) (h3 j (a + d + 1) (by omega))
  intro a b hab
  have hab' : F.fr j a.val = F.fr j b.val := hab
  by_contra hne
  have hne' : a.val ≠ b.val := fun h => hne (Fin.ext h)
  have ha := a.isLt
  have hb := b.isLt
  rcases lt_or_gt_of_ne hne' with h | h
  · have := key (b.val - a.val - 1) a.val (by omega)
    rw [show a.val + (b.val - a.val - 1) + 1 = b.val by omega] at this
    exact absurd hab' (ne_of_lt this)
  · have := key (a.val - b.val - 1) b.val (by omega)
    rw [show b.val + (a.val - b.val - 1) + 1 = a.val by omega] at this
    exact absurd hab'.symm (ne_of_lt this)

theorem plEmb_injective (O : Type) [CommRing O] (r K : ℕ) : Function.Injective (plEmb O r K) := by
  apply rename_injective
  intro a b h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.1 (Fin.castAdd_injective _ _ h.2)

theorem restInd_of (C₀ : ℝ) (hK : RestKey C₀) : RestInd C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hB
  have h1 := li_of_kill (X.offSet K j) (fun q : X.Idx p K j (X.restr j b) => X.monTau K j q.1.2.2)
    (fun q => X.wordEl K O j q.1) (hK p n' r K X O S hX hLa hk j b hB)
  set c0 : MvPolynomial (ℤ × Fin r) O := X.Dw O j ^ X.m0 K *
      (∏ i : Fin r, MvPolynomial.X (X.F.fr (j - 1) i.val, (0 : Fin r)) ^
        ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat) with hc0
  have hD : X.Dw O j ≠ 0 := Formalism.MainNotions.G.Joints.StandardMonomialSpace.detX_ne_zero _ (fr_injective X.F hX.valid (j - 1))
  have hc0ne : c0 ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ hD) (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (X_ne_zero _))
  have hc : plEmb O r K c0 ≠ 0 := (map_ne_zero_iff _ (plEmb_injective O r K)).mpr hc0ne
  have h2 := h1.map' (LinearMap.mulLeft O (plEmb O r K c0))
    (LinearMap.ker_eq_bot.mpr fun x y hxy => mul_left_cancel₀ hc hxy)
  have heq : (fun q : X.Idx p K j (X.restr j b) => X.famEl p K O j b q.1) =
      (⇑(LinearMap.mulLeft O ((plEmb O r K) c0)) ∘
        fun q : X.Idx p K j (X.restr j b) => (monomial (X.monTau K j q.1.2.2)) (1 : O) * X.wordEl K O j q.1) := by
    funext q
    simp only [Function.comp, LinearMap.mulLeft_apply]
    unfold Dat.famEl Dat.wordEl Dat.monTau
    rw [map_mul, ← hc0, mul_assoc]
    congr 2
    rw [MvPolynomial.monomial_sum_one, map_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_pow, ← MvPolynomial.X_pow_eq_monomial]
    simp [plEmb]
  rw [heq]
  exact h2

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

