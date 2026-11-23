module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PushLettersIntCastOfIsHomogeneous
section
open MvPolynomial Matrix NumberField
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)

namespace GlobalTheory.Harm

section Free

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {σ ι : Type*}

noncomputable def basisComponent (b : Module.Basis ι R S) (i : ι) (P : MvPolynomial σ S) :
    MvPolynomial σ R :=
  ∑ m ∈ P.support, monomial m (b.repr (AddMonoidAlgebra.coeff P m) i)

theorem coeff_basisComponent (b : Module.Basis ι R S) (i : ι) (P : MvPolynomial σ S)
    (m : σ →₀ ℕ) : AddMonoidAlgebra.coeff (basisComponent b i P) m = b.repr (AddMonoidAlgebra.coeff P m) i := by
  classical
  rw [basisComponent, coeff_sum, Finset.sum_eq_single m]
  · simp
  · intro m' _ h; simp [coeff_monomial, h]
  · intro h; simp [notMem_support_iff.1 h]

theorem exists_eq_sum_basisComponent (b : Module.Basis ι R S) (P : MvPolynomial σ S) :
    ∃ J : Finset ι, P = ∑ i ∈ J, b i • MvPolynomial.map (algebraMap R S) (basisComponent b i P) := by
  classical
  refine ⟨P.support.biUnion fun m => (b.repr (AddMonoidAlgebra.coeff P m)).support, ?_⟩
  ext m
  simp only [coeff_sum, coeff_smul, coeff_map, coeff_basisComponent, smul_eq_mul]
  conv_lhs => rw [← b.linearCombination_repr (AddMonoidAlgebra.coeff P m), Finsupp.linearCombination_apply]
  rw [Finsupp.sum_of_support_subset (s := P.support.biUnion fun m => (b.repr (AddMonoidAlgebra.coeff P m)).support)]
  · exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
  · by_cases hm : m ∈ P.support
    · exact Finset.subset_biUnion_of_mem (fun m => (b.repr (AddMonoidAlgebra.coeff P m)).support) hm
    · simp [notMem_support_iff.1 hm]
  · simp

theorem basisComponent_sum (b : Module.Basis ι R S) (J : Finset ι) (Q : ι → MvPolynomial σ R)
    {i : ι} (hi : i ∈ J) :
    basisComponent b i (∑ j ∈ J, b j • MvPolynomial.map (algebraMap R S) (Q j)) = Q i := by
  classical
  ext m
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coeff_basisComponent, coeff_sum, coeff_smul, coeff_map, smul_eq_mul, mul_comm (b _),
    ← Algebra.smul_def, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single i] <;> simp +contextual [hi]

variable {T : Type*} {p q : ℕ} {κ : Type*} [Fintype κ] {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ}

theorem basisComponent_mem_rowHighest (b : Module.Basis ι R S) (i : ι) {P : Poly S T p q κ}
    (hP : P ∈ rowHighest S c c') : basisComponent b i P ∈ rowHighest R c c' := by
  classical
  obtain ⟨h₁, h₂, h₃⟩ := mem_rowHighest_iff_rowAdd.1 hP
  obtain ⟨J, hJ⟩ := exists_eq_sum_basisComponent b P
  by_cases hi : i ∈ J
  swap
  · have : basisComponent b i P = 0 := by
      rw [← basisComponent_sum b (insert i J)
        (fun j => if j = i then 0 else basisComponent b j P) (Finset.mem_insert_self i J)
        |>.trans (ite_eq_left rfl)]
      congr 1
      rw [Finset.sum_insert hi, ite_eq_left rfl, map_zero, smul_zero, zero_add]
      refine hJ.trans (Finset.sum_congr rfl fun j hj => ?_)
      rw [ite_eq_right (by rintro rfl; exact hi hj)]
    rw [this]; exact zero_mem _
  refine mem_rowHighest_iff_rowAdd.2 ⟨fun t a b' => ?_, fun t r m hm => h₂ t r fun e => hm ?_,
    fun t r r' hr s => ?_⟩
  · have := h₁ t a b'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hJ, map_sum] at this
    simp only [map_smul, ← map_laplacian] at this
    rw [← basisComponent_sum b J (fun j => laplacian t a b' (basisComponent b j P)) hi, this]
    simp [basisComponent]
  · rw [coeff_basisComponent, e]; simp
  · have := h₃ t r r' hr s
    conv_lhs at this => rw [hJ, map_sum]
    simp only [map_smul, ← map_intCast (algebraMap R S), ← map_rowAdd] at this
    rw [← basisComponent_sum b J (fun j => rowAdd t r r' (s : R) (basisComponent b j P)) hi, this]


variable (R S c c') in
theorem span_map_rowHighest [Module.Free R S] :
    Submodule.span S (MvPolynomial.map (algebraMap R S) ''
      (rowHighest R (κ := κ) c c' : Set (Poly R T p q κ))) = rowHighest S c c' := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨P, hP, rfl⟩
    exact map_mem_rowHighest _ hP
  · intro P hP
    let b := Module.Free.chooseBasis R S
    obtain ⟨J, hJ⟩ := exists_eq_sum_basisComponent b P
    rw [hJ]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, basisComponent_mem_rowHighest b i hP, rfl⟩)

end Free

section Scale

variable {R : Type*} [CommRing R] {T : Type*} {p q : ℕ} {κ : Type*}

end Scale

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type*} [Field K]
  {T : Type*} {p q n : ℕ}

theorem herm_one_eq_sum (x y : Fin n → E) : herm 1 x y = ∑ k, x k * cc (y k) := by
  simp [herm, Matrix.one_apply]


variable (p q) in
noncomputable def symO (τ : T → E →+* K) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Subalgebra (𝓞 K) (Poly K T p q (Fin n)) :=
  Algebra.adjoin (𝓞 K)
    ({P | ∃ t a, ∃ v ∈ Λ, P = xForm t a fun k => τ t (v k)} ∪
      {P | ∃ t b, ∃ v ∈ Λ, P = yForm t b fun k => τ t (cc (v k))})

noncomputable def Ha (τ : T → E →+* K) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 K) (Poly K T p q (Fin n)) :=
  (rowHighest (R := K) c c').restrictScalars (𝓞 K) ⊓ Subalgebra.toSubmodule (symO p q τ Λ)

variable (τ : T → E →+* K) {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ}
  {Λ Λ' : Submodule (𝓞 E) (Fin n → E)} {P : Poly K T p q (Fin n)}













variable [NumberField K]


variable [Fintype T]






end Lattice

end GlobalTheory.Harm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TorusAtEpsIndep
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.SemicharIndep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem cc_cc (a : E) : cc (cc a) = a := IsCMField.complexConj_apply_apply E a

theorem cc_mul (a b : E) : cc (a * b) = cc a * cc b := map_mul (IsCMField.complexConj E) a b

theorem cc_sub (a b : E) : cc (a - b) = cc a - cc b := map_sub (IsCMField.complexConj E) a b

theorem trace_conj (a : E) : Algebra.trace ℚ E (cc a) = Algebra.trace ℚ E a :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (a : E) (u v : Fin r → E) :
    herm G (a • u) v = a * herm G u v := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem herm_smul_right (G : Matrix (Fin r) (Fin r) E) (a : E) (u v : Fin r → E) :
    herm G u (a • v) = cc a * herm G u v := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, cc_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem herm_add_left (G : Matrix (Fin r) (Fin r) E) (u u' v : Fin r → E) :
    herm G (u + u') v = herm G u v + herm G u' v := by
  simp [herm, add_mul, Finset.sum_add_distrib]

theorem herm_add_right (G : Matrix (Fin r) (Fin r) E) (u v v' : Fin r → E) :
    herm G u (v + v') = herm G u v + herm G u v' := by
  simp [herm, cc, mul_add, Finset.sum_add_distrib]

theorem cc_herm {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a) (u v : Fin r → E) :
    cc (herm G u v) = herm G v u := by
  have h : cc (herm G u v) = ∑ a, ∑ b, cc (u a * G a b * cc (v b)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [herm, cc, map_sum]
  rw [h, herm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [cc_mul, cc_mul, cc_cc, hG]; ring

noncomputable def B (X : Data E r) (u v : Fin r → E) : ℚ :=
  Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v)

theorem B_skew (X : Data E r) (u v : Fin r → E) : B X u v = -B X v u := by
  unfold B
  rw [← trace_conj, ← map_neg, cc_mul, cc_herm X.Gm_herm, X.ξ0_im, neg_mul]

theorem B_adj (X : Data E r) (a : E) (u v : Fin r → E) : B X (a • u) v = B X u (cc a • v) := by
  unfold B
  rw [herm_smul_left, herm_smul_right, cc_cc]

theorem B_add_left (X : Data E r) (u u' v : Fin r → E) : B X (u + u') v = B X u v + B X u' v := by
  unfold B
  rw [herm_add_left, mul_add, map_add (f := _)]

theorem B_add_right (X : Data E r) (u v v' : Fin r → E) : B X u (v + v') = B X u v + B X u v' := by
  unfold B
  rw [herm_add_right, mul_add, map_add (f := _)]

theorem B_sub_smul (X : Data E r) (a b : E) (u v : Fin r → E) :
    B X u ((a - b) • v) = B X u (a • v) - B X u (b • v) := by
  unfold B
  rw [herm_smul_right, herm_smul_right, herm_smul_right, cc_sub, sub_mul, mul_sub, map_sub]

theorem B_swap (X : Data E r) (a : E) (u v : Fin r → E) : B X v (a • u) = -B X u (cc a • v) := by
  rw [B_skew, B_adj]

theorem EFf_eq (X : Data E r) (u v : Fin r → E) : EFf X.ξ0 X.Gm u v = -B X u v := by
  rw [EFf, neg_mul, map_neg, B]

theorem B_int (X : DataX E r) {u v : Fin r → E} (hu : u ∈ X.Λ) (hv : v ∈ X.Λ) :
    ∃ k : ℤ, B X.toData u v = k := by
  obtain ⟨k, hk⟩ := X.EF_int u hu v hv
  rw [EFf_eq] at hk
  exact ⟨-k, by push_cast; linarith⟩

theorem exists_half (X : DataX E r) (y : Fin r → E)
    (hy : ∀ u ∈ X.Λ, ∃ k : ℤ, B X.toData u y = 2 * k) :
    ∃ x ∈ X.Λ, ∀ u ∈ X.Λ, B X.toData u y = 2 * B X.toData u x := by
  choose! f hf using hy
  let φ : X.Λ →+ ℤ := AddMonoidHom.mk' (fun u => f u) (fun u v => by
    have h1 := hf _ (u + v).2
    have h2 := hf _ u.2
    have h3 := hf _ v.2
    rw [Submodule.coe_add, B_add_left, h2, h3] at h1
    have : ((f ((u : Fin r → E) + v) : ℤ) : ℚ) = f u + f v := by linarith
    exact_mod_cast this)
  obtain ⟨x, hx, h⟩ := X.EF_perf φ
  refine ⟨x, hx, fun u hu => ?_⟩
  have h1 := h ⟨u, hu⟩
  rw [EFf_eq, ← B_skew] at h1
  rw [hf u hu, ← h1]
  rfl

def Par (X : Data E r) (w : 𝓞 E) : Prop :=
  ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, B X u (((w : E) - cc (w : E)) • v) - B X u v = 2 * k

theorem smul_mem (X : Data E r) (w : 𝓞 E) {v : Fin r → E} (hv : v ∈ X.Λ) : (w : E) • v ∈ X.Λ :=
  X.Λ.smul_mem w hv

theorem cc_smul_mem (X : Data E r) (w : 𝓞 E) {v : Fin r → E} (hv : v ∈ X.Λ) :
    cc (w : E) • v ∈ X.Λ :=
  X.Λ.smul_mem (IsCMField.ringOfIntegersComplexConj E w) hv

theorem parity_eq (X : DataX E r) {w w' : 𝓞 E} (hw : Par X.toData w) (hw' : Par X.toData w')
    {v : Fin r → E} (hv : v ∈ X.Λ) :
    ∃ k : ℤ, B X.toData v ((w : E) • v) - B X.toData v ((w' : E) • v) = 2 * k := by
  obtain ⟨x, hx, h⟩ := exists_half X ((((w : E) - cc (w : E)) - ((w' : E) - cc (w' : E))) • v)
    (fun u hu => by
      obtain ⟨k, hk⟩ := hw u hu v hv
      obtain ⟨l, hl⟩ := hw' u hu v hv
      refine ⟨k - l, ?_⟩
      rw [B_sub_smul]; push_cast; linarith)
  have h1 := h v hv
  rw [B_sub_smul, B_sub_smul, B_sub_smul] at h1
  have h2 := B_swap X.toData (w : E) v v
  have h3 := B_swap X.toData (w' : E) v v
  obtain ⟨k, hk⟩ := hw v hv x hx
  have hm : (cc (w : E) - (w : E)) • v ∈ X.Λ := by
    rw [sub_smul]; exact sub_mem (cc_smul_mem X.toData w hv) (smul_mem X.toData w hv)
  have h4 := h _ hm
  rw [B_adj, B_adj, cc_sub, cc_cc, smul_smul] at h4
  have h5 := B_swap X.toData
    (((w : E) - cc (w : E)) * (((w : E) - cc (w : E)) - ((w' : E) - cc (w' : E)))) v v
  have h6 : cc (((w : E) - cc (w : E)) * (((w : E) - cc (w : E)) - ((w' : E) - cc (w' : E)))) =
      ((w : E) - cc (w : E)) * (((w : E) - cc (w : E)) - ((w' : E) - cc (w' : E))) := by
    simp only [cc_mul, cc_sub, cc_cc]; ring
  rw [h6] at h5
  refine ⟨-k, ?_⟩
  push_cast
  linarith

theorem cos_sign {s : ℝ} (hs : s = 1 ∨ s = -1) (k : ℤ) :
    Real.cos (Real.pi * (s * (((k : ℚ)) : ℝ))) = ((k.negOnePow : ℤ) : ℝ) := by
  have h := Real.cos_int_mul_pi k
  rw [← Int.cast_negOnePow] at h
  rcases hs with rfl | rfl
  · rw [← h]; congr 1; push_cast; ring
  · rw [← h, ← Real.cos_neg]; congr 1; push_cast; ring

theorem eps_val {X : Data E r} {x : Frame X.Ψ r} (A : TorusAt X x) {v : Fin r → E} (hv : v ∈ X.Λ)
    {k : ℤ} (hk : B X v ((A.w0 : E) • v) = k) : A.T.eps (A.φ v) = (k.negOnePow : ℤ) := by
  have h := A.eps_eq v hv
  rw [A.im_eq v hv _ (smul_mem X A.w0 hv)] at h
  unfold B at hk
  rw [hk, cos_sign A.sg_pm] at h
  exact_mod_cast h

theorem par_of_torusAt (X : DataX E r) {x : Frame X.Ψ r} (A : TorusAt X.toData x) :
    Par X.toData A.w0 := by
  intro u hu v hv
  have huv := add_mem hu hv
  obtain ⟨a, ha⟩ := B_int X hu (smul_mem X.toData A.w0 hu)
  obtain ⟨b, hb⟩ := B_int X hv (smul_mem X.toData A.w0 hv)
  obtain ⟨c, hc⟩ := B_int X huv (smul_mem X.toData A.w0 huv)
  obtain ⟨d, hd⟩ := B_int X hu hv
  have h := A.T.eps_add (A.φ u) ((A.lat _).2 ⟨u, hu, rfl⟩) (A.φ v) ((A.lat _).2 ⟨v, hv, rfl⟩)
  have hd' := hd
  unfold B at hd'
  rw [← map_add (f := _), eps_val A hu ha, eps_val A hv hb, eps_val A huv hc, A.im_eq u hu v hv, hd',
    cos_sign A.sg_pm] at h
  have h1 : c.negOnePow = (a + b + d).negOnePow := by
    rw [Int.negOnePow_add, Int.negOnePow_add]
    ext
    push_cast
    exact_mod_cast h
  obtain ⟨k, hk⟩ := (Int.negOnePow_eq_iff _ _).1 h1
  refine ⟨k, ?_⟩
  rw [smul_add, B_add_left, B_add_right, B_add_right, ha, hb, B_swap X.toData _ u v] at hc
  have hk' : (c : ℚ) - (a + b + d) = k + k := by exact_mod_cast hk
  rw [B_sub_smul]
  linarith

end GlobalTheory.SemicharIndep

namespace GlobalTheory


open SemicharIndep in
theorem torusAt_eps_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∀ (x x' : Frame X.Ψ r) (A : TorusAt X.toData x) (A' : TorusAt X.toData x') (γ : GL (Fin r) E), IsUStab X.Gm X.Λ γ → ∀ v ∈ X.Λ, A'.T.eps (A'.φ ((γ : Matrix (Fin r) (Fin r) E).mulVec v)) = A.T.eps (A.φ v) := by
  intro E _ _ _ r X _ x x' A A' γ hγ v hv
  obtain ⟨a, ha⟩ := B_int X hv (smul_mem X.toData A.w0 hv)
  obtain ⟨b, hb⟩ := B_int X hv (smul_mem X.toData A'.w0 hv)
  have hb' : B X.toData ((γ : Matrix (Fin r) (Fin r) E).mulVec v)
      ((A'.w0 : E) • (γ : Matrix (Fin r) (Fin r) E).mulVec v) = b := by
    rw [← hb, B, B, ← Matrix.mulVec_smul, hγ.1]
  rw [eps_val A hv ha, eps_val A' ((hγ.2 v).1 hv) hb']
  obtain ⟨k, hk⟩ := parity_eq X (par_of_torusAt X A') (par_of_torusAt X A) hv
  rw [ha, hb] at hk
  have hk' : b - a = 2 * k := by exact_mod_cast hk
  rw [(Int.negOnePow_eq_iff b a).2 ⟨k, by omega⟩]

end GlobalTheory
end

