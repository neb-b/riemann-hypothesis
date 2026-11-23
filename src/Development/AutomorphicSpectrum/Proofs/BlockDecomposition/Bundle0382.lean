module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumMemOfStable
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.InjHw

variable {n : ℕ}

theorem exp_mem_unitary (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose]
  have h : ((s : ℂ) • X)ᴴ = -((s : ℂ) • X) := by
    rw [conjTranspose_smul, hX]
    simp
  have hc : Commute ((s : ℂ) • X) (-((s : ℂ) • X)) := (Commute.refl _).neg_right
  rw [h, ← Matrix.exp_add_of_commute _ _ hc]
  simp

theorem single_conjT (a b : Fin n) (c : ℂ) :
    (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ)ᴴ = Matrix.single b a (star c) := by
  ext i j
  simp only [conjTranspose_apply, Matrix.single_apply]
  by_cases h : a = j ∧ b = i
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg (fun hh => h ⟨hh.2, hh.1⟩)]
    simp

theorem single_negI (a b : Fin n) (c : ℂ) :
    (Matrix.single a b (-c) : Matrix (Fin n) (Fin n) ℂ) = -Matrix.single a b c := by
  ext i j
  simp only [Matrix.neg_apply, Matrix.single_apply]
  split_ifs <;> simp

def expU (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨NormedSpace.exp ((s : ℂ) • X), exp_mem_unitary X hX s⟩

section V

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)} {Kf : Fin n → Fin n → Module.End ℂ V}

theorem deriv_expU (h : IsDerivK σ Kf) (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (w : V) :
    HasDerivAt (fun s : ℝ => σ (expU X hX s) w) (∑ a, ∑ b, X a b • Kf a b w) 0 := by
  obtain ⟨S, _, hw, _, _, hd⟩ := h.2 w
  exact hd X (expU X hX) (fun _ => rfl) w hw

theorem sum_mem_of_stable (h : IsDerivK σ Kf) (R : Submodule ℂ V) [FiniteDimensional ℂ R]
    (hR : ∀ k, ∀ w ∈ R, σ k w ∈ R) (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) {w : V} (hw : w ∈ R) :
    ∑ a, ∑ b, X a b • Kf a b w ∈ R := by
  have hd := deriv_expU h X hX w
  have hcl : IsClosed (R : Set V) := Submodule.closed_of_finiteDimensional R
  have ht := hasDerivAt_iff_tendsto_slope_zero.1 hd
  refine hcl.mem_of_tendsto ht (Filter.Eventually.of_forall fun s => ?_)
  have : s⁻¹ • (σ (expU X hX (0 + s)) w - σ (expU X hX 0) w) ∈ R.restrictScalars ℝ :=
    Submodule.smul_mem _ _ (sub_mem (hR _ _ hw) (hR _ _ hw))
  exact this

theorem sum_single (w : V) (a b : Fin n) (c : ℂ) :
    ∑ x, ∑ y, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) x y • Kf x y w = c • Kf a b w := by
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro y _ hy
    rw [Matrix.single_apply, if_neg (fun hh => hy hh.2.symm), zero_smul]
  · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [Matrix.single_apply, if_neg (fun hh => hx hh.1.symm), zero_smul]
  · simp

theorem entry_mem (h : IsDerivK σ Kf) (R : Submodule ℂ V) [FiniteDimensional ℂ R]
    (hR : ∀ k, ∀ w ∈ R, σ k w ∈ R) (a b : Fin n) {w : V} (hw : w ∈ R) : Kf a b w ∈ R := by
  have h1 : (Matrix.single a b (1 : ℂ) - Matrix.single b a 1)ᴴ = -(Matrix.single a b (1 : ℂ) - Matrix.single b a 1) := by
    rw [conjTranspose_sub, single_conjT, single_conjT, star_one, neg_sub]
  have h2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
      -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
    rw [conjTranspose_add, single_conjT, single_conjT, Complex.star_def, Complex.conj_I, single_negI, single_negI, neg_add,
      add_comm]
  have m1 := sum_mem_of_stable h R hR _ h1 hw
  have m2 := sum_mem_of_stable h R hR _ h2 hw
  have e1 : ∑ x, ∑ y, (Matrix.single a b (1 : ℂ) - Matrix.single b a 1 : Matrix (Fin n) (Fin n) ℂ) x y • Kf x y w =
      Kf a b w - Kf b a w := by
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, sum_single, one_smul]
  have e2 : ∑ x, ∑ y, (Matrix.single a b Complex.I + Matrix.single b a Complex.I : Matrix (Fin n) (Fin n) ℂ) x y • Kf x y w =
      Complex.I • Kf a b w + Complex.I • Kf b a w := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, sum_single]
  rw [e1] at m1
  rw [e2] at m2
  have m3 := R.smul_mem (-Complex.I) m2
  have m4 := R.smul_mem (1 / 2 : ℂ) (R.add_mem m1 m3)
  have e3 : (1 / 2 : ℂ) • (Kf a b w - Kf b a w + -Complex.I • (Complex.I • Kf a b w + Complex.I • Kf b a w)) = Kf a b w := by
    rw [smul_add (-Complex.I), smul_smul, smul_smul]
    have : -Complex.I * Complex.I = 1 := by simp
    rw [this, one_smul, one_smul, sub_add_add_cancel, ← two_smul ℂ, smul_smul]
    norm_num
  rwa [e3] at m4

theorem weight_of_torus (h : IsDerivK σ Kf) (μ : Fin n → ℤ) {v : V}
    (hv : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → σ k v = (∏ a, z a ^ μ a) • v)
    (a : Fin n) : Kf a a v = ((μ a : ℝ) : ℂ) • v := by
  have hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I) := by
    rw [single_conjT, Complex.star_def, Complex.conj_I, single_negI]
  have hd := deriv_expU (Kf := Kf) h _ hX v
  rw [sum_single] at hd
  have hk : ∀ s : ℝ, (expU _ hX s).1 = diagonal (fun c => if c = a then Complex.exp (s * Complex.I) else 1) := by
    intro s
    have e : (s : ℂ) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ) =
        diagonal (fun c => if c = a then (s : ℂ) * Complex.I else 0) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        by_cases hc : i = a
        · subst hc
          simp
        · simp [Matrix.single_apply, hc, Ne.symm hc]
      · rw [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, Matrix.single_apply,
          if_neg (fun hh => hij (hh.1.symm.trans hh.2)), smul_zero]
    show NormedSpace.exp _ = _
    rw [e, Matrix.exp_diagonal]
    congr 1
    funext c
    split_ifs with hc <;> simp [hc, Complex.exp_eq_exp_ℂ]
  have hf : (fun s : ℝ => σ (expU _ hX s) v) =
      fun s : ℝ => Complex.exp ((s : ℂ) * (Complex.I * ((μ a : ℝ) : ℂ))) • v := by
    funext s
    rw [hv _ _ (hk s), Finset.prod_eq_single a]
    · simp only [if_true]
      rw [← Complex.exp_int_mul]
      congr 2
      push_cast
      ring
    · intro c _ hc
      simp [hc]
    · simp
  rw [hf] at hd
  have h2 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * (Complex.I * ((μ a : ℝ) : ℂ))) • v)
      ((Complex.I * ((μ a : ℝ) : ℂ)) • v) 0 := by
    have h3 : HasDerivAt (fun y : ℂ => Complex.exp (y * (Complex.I * ((μ a : ℝ) : ℂ))))
        (Complex.exp ((0 : ℂ) * (Complex.I * ((μ a : ℝ) : ℂ))) * (1 * (Complex.I * ((μ a : ℝ) : ℂ)))) 0 :=
      ((hasDerivAt_id (0 : ℂ)).mul_const _).cexp
    have h4 := (h3.comp_ofReal).smul_const v
    simpa using h4
  have e := hd.unique h2
  calc Kf a a v = (-Complex.I) • (Complex.I • Kf a a v) := by rw [smul_smul]; simp
    _ = ((μ a : ℝ) : ℂ) • v := by rw [e, smul_smul, ← mul_assoc]; simp

end V

section Main

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem gl_kF {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : IsPair E1 E2) : Formalism.REAL.GlRel (kF E1 E2) := by
  intro a b c d
  have h1 := h.gl1 a b c d
  have h2 := h.gl2 a b c d
  have c1 := h.comm a b c d
  have c2 := h.comm c d a b
  have e : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [kF, add_mul, mul_add]
    rw [c1, c2]
    abel
  rw [e, h1, h2]
  simp only [kF]
  split_ifs <;> abel

theorem weight_shift {K : Fin n → Fin n → Module.End ℂ V} (hg : Formalism.REAL.GlRel K) (μ : Fin n → ℤ) {v : V}
    (hv : ∀ c, K c c v = ((μ c : ℝ) : ℂ) • v) {a b : Fin n} (hab : a ≠ b) (c : Fin n) :
    K c c (K a b v) =
      (((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℤ) : ℝ) : ℂ) • K a b v := by
  have e : K c c (K a b v) = K a b (K c c v) +
      ((if c = a then K c b else 0) - (if b = c then K a c else 0)) v := by
    rw [← hg c c a b]
    simp [Module.End.mul_apply]
  rw [e, hv c, map_smul]
  by_cases h1 : c = a
  · subst h1
    have h2 : ¬ b = c := fun h => hab h.symm
    have h3 : ¬ c = b := hab
    simp only [↓reduceIte, h2, h3, LinearMap.sub_apply, LinearMap.zero_apply]
    push_cast
    module
  · by_cases h2 : c = b
    · subst h2
      simp only [↓reduceIte, h1, LinearMap.sub_apply, LinearMap.zero_apply]
      push_cast
      module
    · have h3 : ¬ b = c := fun h => h2 h.symm
      simp only [↓reduceIte, h1, h2, h3, sub_zero, LinearMap.zero_apply, add_zero]

def jt (K : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ) : Submodule ℂ V :=
  ⨅ c, (K c c).maxGenEigenspace (χ c)

theorem mem_jt {K : Fin n → Fin n → Module.End ℂ V} {χ : Fin n → ℂ} {v : V} (hv : ∀ c, K c c v = χ c • v) :
    v ∈ jt K χ := by
  refine (Submodule.mem_iInf _).2 fun c => ?_
  rw [Module.End.mem_maxGenEigenspace]
  exact ⟨1, by simp [hv c]⟩

theorem jt_indep {K : Fin n → Fin n → Module.End ℂ V} (hg : Formalism.REAL.GlRel K) : iSupIndep (jt K) := by
  have hc : ∀ i j, Commute (K i i) (K j j) := by
    intro i j
    have h := hg i i j j
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · have h' : ¬ j = i := fun h => hij h.symm
      rw [if_neg hij, if_neg h', sub_zero] at h
      exact sub_eq_zero.1 h
  exact Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun c => K c c)
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)

def wtC (μ : Fin n → ℤ) : Fin n → ℂ := fun a => ((μ a : ℝ) : ℂ)

theorem wtC_injective : Function.Injective (wtC (n := n)) := by
  intro x y h
  funext c
  have := congrFun h c
  simpa [wtC] using this

end Main

end GlobalTheory.CompanionTheory.RealCount.InjHw
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupEqOfIrreducibleSubquotient
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenCore

theorem sup_eq_of_isIrreducible_subQuot :
    ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (A B E : Subrepresentation ρ), B ≤ A → (subQuot A B).IsIrreducible → E ≤ A → ¬ E ≤ B →
      E ⊔ B = A := by
  intro G V _ _ _ ρ A B E hBA hirr hEA hEB
  haveI : IsSimpleOrder (Subrepresentation (GlobalTheory.SmGL.subQuot A B)) := hirr
  refine le_antisymm (sup_le hEA hBA) ?_
  let P := Submodule.comap A.toSubmodule.subtype B.toSubmodule
  let S : Submodule ℂ (A.toSubmodule ⧸ P) :=
    Submodule.map P.mkQ (Submodule.comap A.toSubmodule.subtype (E ⊔ B).toSubmodule)
  have hS : ∀ (g : G) ⦃q : A.toSubmodule ⧸ P⦄, q ∈ S →
      GlobalTheory.SmGL.subQuot A B g q ∈ S := by
    intro g q hq
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hq
    exact Submodule.mem_map.mpr
      ⟨⟨ρ g y, A.apply_mem_toSubmodule g y.2⟩, (E ⊔ B).apply_mem_toSubmodule g (v := (y : V)) hy, rfl⟩
  let W : Subrepresentation (GlobalTheory.SmGL.subQuot A B) := ⟨S, hS⟩
  obtain ⟨e, heE, heB⟩ := SetLike.not_le_iff_exists.mp hEB
  have hea : e ∈ A.toSubmodule := hEA heE
  have heEB : e ∈ (E ⊔ B).toSubmodule := (le_sup_left : E ≤ E ⊔ B) heE
  rcases IsSimpleOrder.eq_bot_or_eq_top W with hW | hW
  · exfalso
    let Z : Subrepresentation (GlobalTheory.SmGL.subQuot A B) :=
      ⟨⊥, fun g q hq => by
        rw [Submodule.mem_bot] at hq ⊢
        rw [hq, map_zero]⟩
    have hmem : Submodule.Quotient.mk (p := P) ⟨e, hea⟩ ∈ W := by
      show _ ∈ S
      exact Submodule.mem_map.mpr ⟨⟨e, hea⟩, heEB, rfl⟩
    rw [hW] at hmem
    have hZ : Submodule.Quotient.mk (p := P) ⟨e, hea⟩ ∈ Z := (bot_le : ⊥ ≤ Z) hmem
    have hZ' : Submodule.Quotient.mk (p := P) ⟨e, hea⟩ ∈ (⊥ : Submodule ℂ (A.toSubmodule ⧸ P)) := hZ
    have h0 : Submodule.Quotient.mk (p := P) ⟨e, hea⟩ = 0 := (Submodule.mem_bot ℂ).mp hZ'
    have heP : (⟨e, hea⟩ : A.toSubmodule) ∈ P := (Submodule.Quotient.mk_eq_zero P).mp h0
    exact heB heP
  · intro x hx
    have hxA : x ∈ A.toSubmodule := hx
    let T : Subrepresentation (GlobalTheory.SmGL.subQuot A B) :=
      ⟨⊤, fun _ _ _ => Submodule.mem_top⟩
    have hT : Submodule.Quotient.mk (p := P) ⟨x, hxA⟩ ∈ W := by
      rw [hW]
      exact (le_top : T ≤ ⊤)
        (show Submodule.Quotient.mk (p := P) ⟨x, hxA⟩ ∈ (⊤ : Submodule ℂ (A.toSubmodule ⧸ P)) from
          Submodule.mem_top)
    have hT' : Submodule.Quotient.mk (p := P) ⟨x, hxA⟩ ∈ S := hT
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hT'
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq] at hyx
    have hb : (y : V) - x ∈ B.toSubmodule := hyx
    have hb' : (y : V) - x ∈ (E ⊔ B).toSubmodule := (le_sup_right : B ≤ E ⊔ B) hb
    have hy' : (y : V) ∈ (E ⊔ B).toSubmodule := hy
    have hsub := (E ⊔ B).toSubmodule.sub_mem hy' hb'
    rw [sub_sub_cancel] at hsub
    exact hsub

end GlobalTheory.CompanionTheory.GenCore
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductRankLeOne
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.TensorRank

theorem rank_piTensorProduct_le_one {α : Type} [Fintype α] (M : α → Type)
    [∀ a, AddCommGroup (M a)] [∀ a, Module ℂ (M a)]
    (h : ∀ a, Module.rank ℂ (M a) ≤ 1) : Module.rank ℂ (⨂[ℂ] a, M a) ≤ 1 := by
  choose v₀ hv₀ using fun a => rank_le_one_iff.mp (h a)
  rw [rank_le_one_iff]
  refine ⟨PiTensorProduct.tprod ℂ v₀, fun x => ?_⟩
  refine PiTensorProduct.induction_on x ?_ ?_
  · intro r f
    choose c hc using fun a => hv₀ a (f a)
    refine ⟨r * ∏ a, c a, ?_⟩
    have hf : f = fun a => c a • v₀ a := funext fun a => (hc a).symm
    rw [hf, MultilinearMap.map_smul_univ, mul_smul]
    simp only [RingHom.id_apply]
  · rintro x y ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r + s, by rw [add_smul, hr, hs]⟩

end GlobalTheory.CompanionTheory.TensorRank
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwKerPolyBallLeOfValuationLe
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem polyBall_le_of_valuation_le {n : ℕ} {s₁ s₂ : kˣ}
    (h : valuation k (s₁ : k) ≤ valuation k (s₂ : k)) : polyBall n s₁ ≤ polyBall n s₂ := by
  intro x hx i
  exact le_trans (show valuation k (Multiplicative.toAdd x i) ≤ valuation k (s₁ : k) from hx i) h

theorem twKer_polyBall_le_of_valuation_le (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (a : Fin n → k) {s₁ s₂ : kˣ}
    (h : valuation k (s₁ : k) ≤ valuation k (s₂ : k)) :
    twKer ρ (polyBall n s₁) (resChr ψ a (polyBall n s₁)) ≤
      twKer ρ (polyBall n s₂) (resChr ψ a (polyBall n s₂)) := by
  apply Submodule.span_mono
  rintro w ⟨m, u, rfl⟩
  exact ⟨⟨m.1, polyBall_le_of_valuation_le h m.2⟩, u, rfl⟩

theorem resChr_polyBall_eq (ψ : AddChar k Circle) {n : ℕ} {c s : kˣ}
    (hc : ∀ y ∈ cball c, ψ y = 1) {a b : Fin n → k}
    (hab : ∀ i, (a - b) i ∈ cball (c * s⁻¹)) :
    resChr ψ a (polyBall n s) = resChr ψ b (polyBall n s) := by
  ext x
  have hx : ∀ i, valuation k ((Multiplicative.toAdd x.1) i) ≤ valuation k (s : k) := x.2
  have hd : (a - b) ⬝ᵥ Multiplicative.toAdd x.1 ∈ cball c := by
    show valuation k _ ≤ valuation k (c : k)
    unfold dotProduct
    refine Valuation.map_sum_le _ fun i _ => ?_
    rw [Valuation.map_mul]
    calc valuation k ((a - b) i) * valuation k ((Multiplicative.toAdd x.1) i)
        ≤ valuation k ((c * s⁻¹ : kˣ) : k) * valuation k (s : k) := mul_le_mul' (hab i) (hx i)
      _ = valuation k (c : k) := by rw [← Valuation.map_mul, ← Units.val_mul, inv_mul_cancel_right]
  have key : a ⬝ᵥ Multiplicative.toAdd x.1 = b ⬝ᵥ Multiplicative.toAdd x.1 + (a - b) ⬝ᵥ Multiplicative.toAdd x.1 := by
    rw [sub_dotProduct]
    abel
  show ((Circle.toUnits (ψ (a ⬝ᵥ Multiplicative.toAdd x.1)) : ℂˣ) : ℂ) =
    ((Circle.toUnits (ψ (b ⬝ᵥ Multiplicative.toAdd x.1)) : ℂˣ) : ℂ)
  rw [key, AddChar.map_add_eq_mul, hc _ hd, mul_one]

theorem exists_unit_valuation_ge {ι : Type} (S : ι → kˣ) (T : Finset ι) :
    ∃ s : kˣ, ∀ a ∈ T, valuation k (S a : k) ≤ valuation k (s : k) := by
  classical
  rcases T.eq_empty_or_nonempty with hT | hT
  · exact ⟨1, by simp [hT]⟩
  · obtain ⟨a₀, -, ha₀⟩ := T.exists_max_image (fun a => valuation k (S a : k)) hT
    exact ⟨S a₀, ha₀⟩

end

private theorem isHecke_div_and_resEtaPow_div {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (hψ : Continuous ψ) : ∃ c : kˣ, ∀ y ∈ GlobalTheory.SplitWeil.cball c, ψ y = 1 := by
  have hU : IsOpen {z : Circle | 0 < (z : ℂ).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)
  have hW : ψ ⁻¹' {z : Circle | 0 < (z : ℂ).re} ∈ 𝓝 (0 : k) := by
    apply hψ.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact hU.mem_nhds (by simp)
  have hW' : {f : Fin 1 → k | f 0 ∈ ψ ⁻¹' {z : Circle | 0 < (z : ℂ).re}} ∈ 𝓝 (0 : Fin 1 → k) :=
    (continuous_apply 0).continuousAt.preimage_mem_nhds hW
  obtain ⟨c, hcW⟩ := GlobalTheory.SplitWeil.FourierPi.exists_box_subset hW'
  refine ⟨c, fun y hy => ?_⟩
  have hmem : ∀ m : ℕ, m • y ∈ GlobalTheory.SplitWeil.cball c := by
    intro m
    induction m with
    | zero => simp only [zero_smul, GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, map_zero]; exact zero_le'
    | succ m ih =>
      rw [succ_nsmul]
      simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq] at ih hy ⊢
      exact Valuation.map_add_le _ ih hy
  have hpos : ∀ m : ℕ, 0 < (((ψ y) ^ m : Circle) : ℂ).re := by
    intro m
    have := hcW (show (fun _ : Fin 1 => m • y) ∈ GlobalTheory.SplitWeil.FourierPi.box (Fin 1) c from fun i _ => hmem m)
    rw [← AddChar.map_nsmul_eq_pow]
    exact this
  have hn : ∀ w : Circle, (w : ℂ).re * (w : ℂ).re + (w : ℂ).im * (w : ℂ).im = 1 := by
    intro w
    rw [← Complex.normSq_apply]
    exact Circle.normSq_coe w
  have hsq : ∀ w : Circle, ((w ^ 2 : Circle) : ℂ).re = 2 * (w : ℂ).re ^ 2 - 1 := by
    intro w
    have h2 : ((w ^ 2 : Circle) : ℂ) = (w : ℂ) * (w : ℂ) := by rw [pow_two]; rfl
    rw [h2, Complex.mul_re]
    nlinarith [hn w]
  have hle1 : ∀ w : Circle, (w : ℂ).re ≤ 1 := fun w => by nlinarith [hn w]
  have hstep : ∀ j : ℕ, (ψ y) ^ (2 ^ (j + 1)) = ((ψ y) ^ (2 ^ j)) ^ 2 := fun j => by rw [pow_succ, pow_mul]
  have hgrow : ∀ j : ℕ, (2 : ℝ) ^ j * (1 - ((ψ y : Circle) : ℂ).re) ≤ 1 - ((((ψ y) ^ (2 ^ j) : Circle)) : ℂ).re := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [hstep j, hsq]
      have h0 := hpos (2 ^ j)
      have h1 := hle1 ((ψ y) ^ (2 ^ j))
      rw [pow_succ]
      nlinarith
  have hx0 : 1 ≤ ((ψ y : Circle) : ℂ).re := by
    by_contra hlt
    push_neg at hlt
    have hd : 0 < 1 - ((ψ y : Circle) : ℂ).re := by linarith
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / (1 - ((ψ y : Circle) : ℂ).re)) (by norm_num : (1 : ℝ) < 2)
    have h1 := hgrow j
    have h2 := hpos (2 ^ j)
    have h3 : 1 < (2 : ℝ) ^ j * (1 - ((ψ y : Circle) : ℂ).re) := by
      rw [div_lt_iff₀ hd] at hj
      linarith
    linarith
  have hre : ((ψ y : Circle) : ℂ).re = 1 := le_antisymm (hle1 _) hx0
  have him : ((ψ y : Circle) : ℂ).im = 0 := by nlinarith [hn (ψ y)]
  apply Circle.ext
  apply Complex.ext
  · simp [hre]
  · simp [him]

theorem exists_polyBall_twKer_uniform : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ →
    ∀ {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (v : V) (t : kˣ),
    (∀ a : Fin n → k, ∃ s : kˣ, v ∈ twKer ρ (polyBall n s) (resChr ψ a (polyBall n s))) →
    ∃ s : kˣ, ∀ a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall n t →
      v ∈ twKer ρ (polyBall n s) (resChr ψ a (polyBall n s)) := by
  intro k _ _ _ _ ψ hψ n V _ _ ρ v t hv
  obtain ⟨c, hc⟩ := isHecke_div_and_resEtaPow_div ψ hψ
  choose S hS using hv
  obtain ⟨T, hT⟩ := (GlobalTheory.SplitWeil.FourierPi.isCompact_box (n := Fin n) t).elim_finite_subcover
    (fun a : Fin n → k => (fun b => b - a) ⁻¹' GlobalTheory.SplitWeil.FourierPi.box (Fin n) (c * (S a)⁻¹))
    (fun a => (GlobalTheory.SplitWeil.FourierPi.isOpen_box _).preimage (continuous_id.sub continuous_const))
    (fun b _ => Set.mem_iUnion.2 ⟨b, fun i _ => by simp only [sub_self, Pi.zero_apply, GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, map_zero]; exact zero_le'⟩)
  obtain ⟨s, hs⟩ := exists_unit_valuation_ge S T
  refine ⟨s, fun a ha => ?_⟩
  have haK : a ∈ GlobalTheory.SplitWeil.FourierPi.box (Fin n) t := fun i _ => ha i
  obtain ⟨b, hbT, hab⟩ := Set.mem_iUnion₂.1 (hT haK)
  have heq : resChr ψ a (polyBall n (S b)) = resChr ψ b (polyBall n (S b)) :=
    resChr_polyBall_eq ψ hc (fun i => hab i (Set.mem_univ i))
  have h1 := hS b
  rw [← heq] at h1
  exact twKer_polyBall_le_of_valuation_le ψ ρ a (hs b hbT) h1

end GlobalTheory.CompanionTheory.MirFourier

end
end

