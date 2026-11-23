module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0010

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CoeffEvWMem
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

section

variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B] {D N : ℕ}

noncomputable def evW (w : Fin (N + 1) → B) :
    MvPolynomial (UXVar D N) R →ₐ[R] MvPolynomial (Fin (D + 2) × Fin (N + 1)) B :=
  aeval (Sum.elim X fun i => ∑ j, X (i, j) * C (w j))

def CoeffIn (W : Submodule R B) (m : ℕ) (p : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B) : Prop :=
  ∀ β, AddMonoidAlgebra.coeff p β ∈ W ^ m

variable (W : Submodule R B)

theorem coeffIn_mul {m m' : ℕ} {p q : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B}
    (hp : CoeffIn W m p) (hq : CoeffIn W m' q) : CoeffIn W (m + m') (p * q) := fun β => by
  rw [coeff_mul, pow_add]
  exact Submodule.sum_mem _ fun x _ => Submodule.mul_mem_mul (hp _) (hq _)

theorem coeffIn_one : CoeffIn W 0 (1 : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B) := fun β => by
  rw [pow_zero, coeff_one]
  split_ifs
  · exact Submodule.mem_one.2 ⟨1, map_one _⟩
  · exact zero_mem _

theorem coeffIn_pow {m : ℕ} {p : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B}
    (hp : CoeffIn W m p) (k : ℕ) : CoeffIn W (m * k) (p ^ k) := by
  induction k with
  | zero => simpa using coeffIn_one W
  | succ k ih =>
    rw [pow_succ, Nat.mul_succ]
    exact coeffIn_mul W ih hp

theorem coeffIn_prod {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial (Fin (D + 2) × Fin (N + 1)) B)
    (m : ι → ℕ) (h : ∀ i ∈ s, CoeffIn W (m i) (p i)) : CoeffIn W (∑ i ∈ s, m i) (∏ i ∈ s, p i) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simpa using coeffIn_one W) ?_
  intro a s ha ih h
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  exact coeffIn_mul W (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem coeffIn_smul {m : ℕ} {p : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B}
    (hp : CoeffIn W m p) (r : R) : CoeffIn W m (C (algebraMap R B r) * p) := fun β => by
  rw [coeff_C_mul, ← Algebra.smul_def]
  exact Submodule.smul_mem _ r (hp β)

theorem coeffIn_X (u : Fin (D + 2) × Fin (N + 1)) : CoeffIn W 0 (X u : MvPolynomial _ B) := fun β => by
  rw [pow_zero, coeff_X']
  split_ifs
  · exact Submodule.mem_one.2 ⟨1, map_one _⟩
  · exact zero_mem _

theorem coeffIn_lin (w : Fin (N + 1) → B) (hw : ∀ j, w j ∈ W) (i : Fin (D + 2)) :
    CoeffIn W 1 (∑ j, X (i, j) * C (w j) : MvPolynomial (Fin (D + 2) × Fin (N + 1)) B) := fun β => by
  rw [coeff_sum, pow_one]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [mul_comm, coeff_C_mul, coeff_X']
  split_ifs
  · rw [mul_one]
    exact hw j
  · rw [mul_zero]
    exact zero_mem _

private theorem sum_support_inr_eq_xDeg {D N : ℕ} (s : UXVar D N →₀ ℕ) :
    ∑ x ∈ s.support, Sum.elim (fun _ => 0) (fun i => s (Sum.inr i)) x = xDeg s := by
  rw [xDeg, Finset.sum_subset (Finset.subset_univ _), Fintype.sum_sum_type]
  · simp
  · intro x _ hx
    cases x with
    | inl p => rfl
    | inr i => simpa using hx

theorem coeffIn_evW (w : Fin (N + 1) → B) (hw : ∀ j, w j ∈ W) {n : ℕ}
    (Q : MvPolynomial (UXVar D N) R) (hx : XHom n Q) : CoeffIn W n (evW w Q) := by
  intro β
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Q.as_sum, map_sum, coeff_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hterm : CoeffIn W n (evW w (monomial s (AddMonoidAlgebra.coeff Q s))) := by
    rw [evW, aeval_monomial, MvPolynomial.algebraMap_apply]
    apply coeffIn_smul
    rw [Finsupp.prod, ← hx s hs, ← sum_support_inr_eq_xDeg s]
    refine coeffIn_prod W s.support _ _ fun x _ => ?_
    cases x with
    | inl p => simpa using coeffIn_pow W (coeffIn_X W p) (s (Sum.inl p))
    | inr i => simpa using coeffIn_pow W (coeffIn_lin W w hw i) (s (Sum.inr i))
  exact hterm β

theorem coeff_evW_mem (w : Fin (N + 1) → B) {n : ℕ} (Q : MvPolynomial (UXVar D N) R)
    (hx : XHom n Q) (β : Fin (D + 2) × Fin (N + 1) →₀ ℕ) :
    AddMonoidAlgebra.coeff (evW w Q) β ∈
      Submodule.span R (Set.range fun s : Fin n → Fin (N + 1) => ∏ k, w (s k)) := by
  have h := coeffIn_evW (Submodule.span R (Set.range w)) w (fun j => Submodule.subset_span ⟨j, rfl⟩) Q hx β
  rw [Submodule.span_pow] at h
  refine Submodule.span_mono ?_ h
  intro a ha
  rw [Set.mem_pow] at ha
  obtain ⟨f, rfl⟩ := ha
  choose s hs using fun k => (f k).2
  refine ⟨s, ?_⟩
  show ∏ k, w (s k) = _
  rw [List.prod_ofFn]
  exact Finset.prod_congr rfl fun k _ => hs k

end

theorem evW_factor {R S B : Type*} [CommRing R] [CommRing S] [CommRing B] [Algebra R S]
    [Algebra R B] [Algebra S B] [IsScalarTower R S B] {D N n : ℕ} (y : Fin (N + 1) → S) (w0 : B)
    (Q : MvPolynomial (UXVar D N) R) (hx : XHom n Q) :
    evW (fun j => algebraMap S B (y j) * w0) Q =
      MvPolynomial.map (algebraMap S B) (evW y Q) * C (w0 ^ n) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Q.as_sum, map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  simp only [evW, aeval_monomial, MvPolynomial.algebraMap_apply, map_mul, map_C, Finsupp.prod,
    map_prod, map_pow]
  rw [← IsScalarTower.algebraMap_apply, mul_assoc]
  congr 1
  rw [← hx s hs, ← sum_support_inr_eq_xDeg s]
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  cases x with
  | inl p => simp
  | inr i =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Sum.elim_inr, map_sum, map_mul, map_X, map_C]
    rw [← mul_pow, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

theorem map_evW_eq {K S : Type*} [Field K] [CommRing S] [Algebra K S] {D N : ℕ} (P : S →+* ℂ)
    (sg : K →+* ℂ) (hP : P.comp (algebraMap K S) = sg) (y : Fin (N + 1) → S)
    (R : MvPolynomial (UXVar D N) K) :
    MvPolynomial.map P (evW (R := K) y R) = Ey (fun j => P (y j)) (MvPolynomial.map sg R) := by
  have h : (MvPolynomial.map P).comp (evW (R := K) (D := D) y).toRingHom =
      (Ey (D := D) (fun j => P (y j))).toRingHom.comp (MvPolynomial.map sg) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [evW, Ey, ← hP]
    · intro i
      cases i <;> simp [evW, Ey]
  exact RingHom.congr_fun h R

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IntNsg
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

private theorem hintIS_log_nrm_of_mem_graded (hd : d.AxH 𝒜) (h : d.S1) {c : ι} {sg : K →+* ℂ} {G : WT}
    {f e : A c} (he : e ∈ 𝒜 c G) (he0 : e ≠ 0) (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0)
    (hI : d.HintIS c sg (fun P => Real.log (d.nrm c G e P))) :
    d.HintIS c sg (fun P => Real.log (d.nrm c G f P)) := by
  have h1 := d.hint_intNorm hd h c sg (ratio (Ω := Ω c) f e) (d.hint_ratio_ne hd he he0 hf hf0)
  have h2 := d.hintIS_lin hd h (φ₁ := fun P => Real.log ‖P (ratio (Ω := Ω c) f e)‖) h1 hI 1 1 0
  refine d.hintIS_congr hd h (ψ := fun P => Real.log (d.nrm c G f P)) h2 ?_
  intro P _
  try dsimp only
  rw [d.hint_log_line hd he he0 hf hf0 P]
  ring

theorem int_Nsg (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (c : ι) (sg : K →+* ℂ) :
    (∀ (G : WT) (f : A c), G ∈ ({d.wL, d.n1 • d.wde, (2 : ℕ) • d.G1, d.wF, d.G2} : Set WT) →
      f ∈ 𝒜 c G → f ≠ 0 →
      MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
        ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
          Real.log (d.nrm c G f P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))) ∧
    (∀ f : A c, f ∈ 𝒜 c d.wL → f ≠ 0 →
      MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
        ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
          Real.log (d.nrm c d.wL f P / d.be c P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))) := by
  obtain ⟨h_et, h_w, h_ta1, ⟨e, he, he0, h_e⟩, h_ta2⟩ := d.hint_chain hd h hI2be c sg
  have hL : ∀ f : A c, f ∈ 𝒜 c d.wL → f ≠ 0 →
      d.HintIS c sg (fun P => Real.log (d.nrm c d.wL f P)) :=
    fun f hf hf0 => hintIS_log_nrm_of_mem_graded d hd h (hd.w_mem (d.jc c) c) (hd.w_base c) hf hf0 h_w
  refine ⟨fun G f hG hf hf0 => ?_, fun f hf hf0 => ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hG
    rcases hG with rfl | rfl | rfl | rfl | rfl
    · exact hL f hf hf0
    · exact hintIS_log_nrm_of_mem_graded d hd h (hd.et_mem c) (hd.et_ne c) hf hf0 h_et
    · exact hintIS_log_nrm_of_mem_graded d hd h (hd.firstSectionMem c) (hd.firstSectionNeZero c) hf hf0 h_ta1
    · exact hintIS_log_nrm_of_mem_graded d hd h he he0 hf hf0 h_e
    · exact hintIS_log_nrm_of_mem_graded d hd h (hd.secondSectionMem c) (hd.secondSectionNeZero c) hf hf0 h_ta2
  · have h3 := d.hintIS_lin hd h (hL f hf hf0) h_w 1 (-1) 0
    have h4 := d.hintIS_lin hd h (φ₂ := fun P => Real.log ‖d.hintU c P‖) h3
      (d.hint_intU hd h c sg) 1 (-1) 0
    refine d.hintIS_congr hd h (ψ := fun P => Real.log (d.nrm c d.wL f P / d.be c P)) h4 ?_
    intro P _
    try dsimp only
    have hpos := hd.nrm_pos c P hf hf0
    have hw := hd.nrm_pos c P (hd.w_mem (d.jc c) c) (hd.w_base c)
    have hU := d.hint_one_le_U hd c P
    have hbe : d.be c P ≠ 0 := by
      rw [d.hint_be_eq hd c P]
      exact (mul_pos hw (lt_of_lt_of_le one_pos hU)).ne'
    rw [Real.log_div hpos.ne' hbe, d.hint_log_be hd c P]
    ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

