module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.ConstCopies
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SemiCharImg
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.PullIopOf

@[expose] public section

-- bundled from Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.CardSmulMem
section
noncomputable section
open scoped BigOperators ComplexConjugate
open Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.L2.Th1.H

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem sum_reps_perm {M P : AddSubgroup V} {S : Finset V} (hS : IsReps M P S) (ℓ : V → V)
    (hP : ∀ x ∈ P, ℓ x ∈ P) (hinj : ∀ x ∈ P, ∀ y ∈ P, ℓ x - ℓ y ∈ M → x - y ∈ M)
    (f : V → ℂ) (hf : ∀ x ∈ P, ∀ y ∈ M, f (x + y) = f x) :
    ∑ x ∈ S, f (ℓ x) = ∑ x ∈ S, f x := by
  obtain ⟨h1, h2, h3⟩ := hS
  have hex : ∀ x ∈ S, ∃ s ∈ S, ℓ x - s ∈ M := fun x hx => h3 _ (hP x (h1 x hx))
  choose! r hr1 hr2 using hex
  have hfr : ∀ x ∈ S, f (ℓ x) = f (r x) := by
    intro x hx
    have := hf (r x) (h1 _ (hr1 x hx)) (ℓ x - r x) (hr2 x hx)
    rwa [add_sub_cancel] at this
  have hinjr : Set.InjOn r S := by
    intro x hx y hy hxy
    refine h2 x hx y hy (hinj x (h1 x hx) y (h1 y hy) ?_)
    have : ℓ x - ℓ y = (ℓ x - r x) - (ℓ y - r y) := by rw [hxy]; abel
    rw [this]; exact M.sub_mem (hr2 x hx) (hr2 y hy)
  have himg : S.image r = S :=
    Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hr1) (by rw [Finset.card_image_of_injOn hinjr])
  calc ∑ x ∈ S, f (ℓ x) = ∑ x ∈ S, f (r x) := Finset.sum_congr rfl hfr
    _ = ∑ y ∈ S.image r, f y := (Finset.sum_image hinjr).symm
    _ = ∑ x ∈ S, f x := by rw [himg]

theorem card_smul_mem {M P : AddSubgroup V} {S : Finset V} (hS : IsReps M P S) {x : V} (hx : x ∈ P) : S.card • x ∈ M := by
  have hc : Nat.card (P ⧸ M.addSubgroupOf P) = S.card := by
    rw [← Nat.card_congr (Equiv.ofBijective _ (repClass_bijective hS))]
    simp
  have h : S.card • (QuotientAddGroup.mk (⟨x, hx⟩ : P) : P ⧸ M.addSubgroupOf P) = 0 := by
    rw [← hc]; exact card_nsmul_eq_zero'
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h
  simpa using h

theorem comm_symm (g : V →ₗ[ℂ] V) (φ : V ≃ₗ[ℂ] V) (h : ∀ x, g (φ x) = φ (g x)) (x : V) : g (φ.symm x) = φ.symm (g x) := by
  apply φ.injective
  rw [← h, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

structure Multipliers (H : Sesq V) (Λ : AddSubgroup V) (δ : V ≃ₗ[ℂ] V) (ℓ ℓ' σ : V →ₗ[ℂ] V) (e : ℕ) : Prop where
  lΛ : ∀ x ∈ Λ, ℓ x ∈ Λ
  l'Λ : ∀ x ∈ Λ, ℓ' x ∈ Λ
  sΛ : ∀ x ∈ Λ, σ x ∈ Λ
  lδ : ∀ x, ℓ (δ x) = δ (ℓ x)
  l'δ : ∀ x, ℓ' (δ x) = δ (ℓ' x)
  sδ : ∀ x, σ (δ x) = δ (σ x)
  adj : ∀ x y, H (ℓ x) y = H x (ℓ' y)
  sadj : ∀ x y, H (σ x) y = H x (σ y)
  rel : ∀ x, ℓ' (ℓ x) = -x + (4 * e) • σ x

variable {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ} {δ Ae : V ≃ₗ[ℂ] V}

theorem comm_cay (hA : ∀ x, Ae x = x - δ.symm x) (g : V →ₗ[ℂ] V) (h : ∀ x, g (δ x) = δ (g x)) (x : V) :
    g (Ae x) = Ae (g x) := by
  rw [hA, hA, map_sub, comm_symm g δ h]

theorem latA_stable (hA : ∀ x, Ae x = x - δ.symm x) (g : V →ₗ[ℂ] V) (hΛ : ∀ x ∈ Λ, g x ∈ Λ)
    (h : ∀ x, g (δ x) = δ (g x)) {y : V} (hy : y ∈ latA Λ δ Ae) : g y ∈ latA Λ δ Ae := by
  unfold latA at hy ⊢
  rw [mem_imgLat_iff, AddSubgroup.mem_inf, mem_imgLat_iff] at hy ⊢
  rw [← comm_symm g Ae (comm_cay hA g h), ← comm_symm g δ h]
  exact ⟨hΛ _ hy.1, hΛ _ hy.2⟩

theorem cayC_comm (hA : ∀ x, Ae x = x - δ.symm x) (g : V →ₗ[ℂ] V) (h : ∀ x, g (δ x) = δ (g x)) (x : V) :
    cayC Ae (g x) = g (cayC Ae x) := by
  unfold cayC
  rw [map_sub, map_smul, comm_symm g Ae (comm_cay hA g h)]

variable {ℓ ℓ' σ : V →ₗ[ℂ] V} {e : ℕ}

theorem phi_conj (hU : UnitaryData H Λ α δ Ae) (hM : Multipliers H Λ δ ℓ ℓ' σ e)
    (he : ∀ x ∈ Λ, e • x ∈ latA Λ δ Ae) (hα : ∀ x ∈ Λ, α (ℓ x) = α x) {x : V} (hx : x ∈ Λ) :
    phiC H α Ae (ℓ x) = conj (phiC H α Ae x) := by
  obtain ⟨hskew, hre, -, -⟩ := phiBasic V H Λ α δ Ae hU
  have h1 : H (cayC Ae (ℓ x)) (ℓ x) = -H (cayC Ae x) x + (4 * e : ℂ) * H (cayC Ae x) (σ x) := by
    rw [cayC_comm hU.cay ℓ hM.lδ, hM.adj, hM.rel, map_add (f := _), map_neg, map_nsmul, nsmul_eq_mul]
    push_cast
    rfl
  have hXre : (H (cayC Ae x) (σ x)).re = 0 := by
    have h2 : H (cayC Ae x) (σ x) = -conj (H (cayC Ae x) (σ x)) := by
      conv_lhs => rw [hskew, cayC_comm hU.cay σ hM.sδ, ← hM.sadj, hU.herm (cayC Ae x) (σ x)]
    have h3 := congrArg Complex.re h2
    simp only [Complex.neg_re, Complex.conj_re] at h3
    linarith
  have hs0 : (H x (σ x)).im = 0 := by
    have h2 : H x (σ x) = conj (H x (σ x)) := by
      conv_lhs => rw [← hM.sadj, hU.herm x (σ x)]
    have h3 := congrArg Complex.im h2
    simp only [Complex.conj_im] at h3
    linarith
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (e : ℝ) * (H (cayC Ae x) (σ x)).im = (n : ℝ) := by
    have hw : Ae.symm (e • x) ∈ Λ := by
      have := he x hx
      unfold latA at this
      rw [mem_imgLat_iff, AddSubgroup.mem_inf] at this
      exact this.1
    rw [← hU.selfDual] at hw
    obtain ⟨n, hn⟩ := hw (σ x) (hM.sΛ x hx)
    refine ⟨n, ?_⟩
    rw [← hn]
    unfold altE cayC
    rw [map_nsmul, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, map_sub, LinearMap.sub_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    simp only [Complex.sub_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, hs0]
    norm_num
  have hX : (4 * e : ℂ) * H (cayC Ae x) (σ x) = (4 * n : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [hXre]
    · have : ((4 * e : ℂ) * H (cayC Ae x) (σ x)).im = 4 * ((e : ℝ) * (H (cayC Ae x) (σ x)).im) := by
        simp [hXre]; ring
      rw [this, hn]
      simp
  have hexp : Complex.exp (-(Real.pi : ℂ) * ((4 * n : ℂ) * Complex.I)) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (-2 * n)
    rw [← this]
    congr 1
    push_cast
    ring
  have hc : conj (H (cayC Ae x) x) = -H (cayC Ae x) x := by
    apply Complex.ext
    · simp [hre x]
    · simp
  have hαc : conj (α x) = α x := by
    rcases hU.semi.1 x hx with h | h <;> rw [h] <;> simp
  unfold phiC
  rw [hα x hx, h1, hX, map_mul, hαc, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal, hc, mul_add,
    Complex.exp_add, hexp, mul_one]

theorem gauss_sq (hU : UnitaryData H Λ α δ Ae) (hM : Multipliers H Λ δ ℓ ℓ' σ e)
    (he : ∀ x ∈ Λ, e • x ∈ latA Λ δ Ae) (hα : ∀ x ∈ Λ, α (ℓ x) = α x) {S : Finset V}
    (hS : IsReps (latA Λ δ Ae) Λ S) : gaussC H α Ae S ^ 2 = 1 := by
  obtain ⟨-, -, -, hwd⟩ := phiBasic V H Λ α δ Ae hU
  have hinj : ∀ x ∈ Λ, ∀ y ∈ Λ, ℓ x - ℓ y ∈ latA Λ δ Ae → x - y ∈ latA Λ δ Ae := by
    intro x hx y hy h
    rw [← map_sub] at h
    have h2 := latA_stable hU.cay ℓ' hM.l'Λ hM.l'δ h
    rw [hM.rel] at h2
    have h3 : (4 * e) • σ (x - y) ∈ latA Λ δ Ae := by
      rw [mul_smul]
      exact AddSubgroup.nsmul_mem _ (he _ (hM.sΛ _ (Λ.sub_mem hx hy))) 4
    have h4 := AddSubgroup.sub_mem _ h3 h2
    have h5 : (4 * e) • σ (x - y) - (-(x - y) + (4 * e) • σ (x - y)) = x - y := by abel
    rwa [h5] at h4
  have hsum := sum_reps_perm hS ℓ hM.lΛ hinj (phiC H α Ae) hwd
  have hreal : conj (gaussC H α Ae S) = gaussC H α Ae S := by
    unfold gaussC
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_inv₀, Complex.conj_ofReal, map_sum, ← hsum]
    congr 1
    exact Finset.sum_congr rfl fun x hx => (phi_conj hU hM he hα (hS.1 x hx)).symm
  have h8 := unitaryGauss V H Λ α δ Ae hU S hS
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp hreal
  rw [hr] at h8 ⊢
  have h8' : (r ^ 2) ^ 4 = 1 := by
    have : ((r ^ 2) ^ 4 : ℝ) = r ^ 8 := by ring
    rw [this]
    exact_mod_cast h8
  have h2 := (pow_eq_one_iff_of_nonneg (sq_nonneg r) (by norm_num)).mp h8'
  exact_mod_cast h2

end Formalism.L2.PairingIndexBounds.Eq.J
end
end

-- bundled from Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.MemStandardThetaLatticeIffAdelicIdeal
section
noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def rowE (D : D7) (N N' : ℕ) : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] (Fin N' → TaylorLogMetric.VC D N 1) where
  toFun z := fun i τ _ j => z τ i j
  invFun w := fun τ i j => w i τ 0 j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv w := by
    funext i τ a j
    rw [Subsingleton.elim a 0]

def colE (D : D7) (N N' : ℕ) : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] (Fin N → TaylorLogMetric.VC D N' 1) where
  toFun z := fun j τ _ i => z τ i j
  invFun w := fun τ i j => w j τ 0 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv w := by
    funext i τ a j
    rw [Subsingleton.elim a 0]

theorem form_row (A : ℝ) (N N' : ℕ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' x y = ∑ i, Ker.formV A D.what₂.Tau N 1 (rowE D N N' x i) (rowE D N N' y i) := by
  simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, rowE, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.univ_unique, Finset.sum_singleton]
  rw [← Finset.sum_div, Finset.sum_comm]

theorem form_col (A : ℝ) (N N' : ℕ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' x y = ∑ j, Ker.formV A D.what₂.Tau N' 1 (colE D N N' x j) (colE D N N' y j) := by
  simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, colE, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.univ_unique, Finset.sum_singleton]
  rw [← Finset.sum_div]
  congr 1
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun τ _ => Finset.sum_comm

theorem formV_pos {A : ℝ} (hA : 0 < A) (n : Type) [Fintype n] (N N' : ℕ) : IsPosDef (Ker.formV A n N N') := by
  intro x hx
  have e : (Ker.formV A n N N' x x).re = (∑ τ, ∑ i, ∑ j, Complex.normSq (x τ i j)) / A := by
    simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, Complex.mul_conj]
    rw [← Complex.ofReal_re ((∑ τ, ∑ i, ∑ j, Complex.normSq (x τ i j)) / A)]
    push_cast
    rfl
  rw [e]
  refine div_pos ?_ hA
  obtain ⟨τ, i, j, h⟩ : ∃ τ i j, x τ i j ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hx (funext fun τ => funext fun i => funext fun j => hno τ i j)
  calc 0 < Complex.normSq (x τ i j) := Complex.normSq_pos.mpr h
    _ ≤ ∑ j, Complex.normSq (x τ i j) :=
        Finset.single_le_sum (f := fun j => Complex.normSq (x τ i j)) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, Complex.normSq (x τ i j) :=
        Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (x τ i j))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ τ, ∑ i, ∑ j, Complex.normSq (x τ i j) :=
        Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, Complex.normSq (x τ i j))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ τ)

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Ker.Base D cc δ)

include B in
theorem area_pos' : 0 < TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂ := by
  have := B.areaOK
  unfold Ker.Base.AreaOK at this
  show 0 < TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)
  rw [this]
  exact Formalism.L2.Th1.F.areaPos_thm B.L

abbrev La0 (_B : Ker.Base D cc δ) (N N' : ℕ) : AddSubgroup (TaylorLogMetric.VC D N N') :=
  TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')

theorem mem_standardThetaLattice_iff_adelicIdeal (N N' : ℕ) (x : TaylorLogMetric.VC D N N') : x ∈ La0 B N N' ↔ ∀ i j, (fun τ => x τ i j) ∈ B.lamM := by
  have := B.lat0OK N N'
  unfold Ker.Base.Lat0OK at this
  show x ∈ TaylorLogMetric.La D B.tor _ _ ↔ _
  rw [this]
  rfl

theorem lat_row (N N' : ℕ) (x : TaylorLogMetric.VC D N N') : x ∈ La0 B N N' ↔ ∀ i, rowE D N N' x i ∈ La0 B N 1 := by
  simp only [mem_standardThetaLattice_iff_adelicIdeal]
  exact ⟨fun h i _ j => h i j, fun h i j => h i 0 j⟩

theorem lat_col (N N' : ℕ) (x : TaylorLogMetric.VC D N N') : x ∈ La0 B N N' ↔ ∀ j, colE D N N' x j ∈ La0 B N' 1 := by
  simp only [mem_standardThetaLattice_iff_adelicIdeal]
  exact ⟨fun h j _ i => h i j, fun h i j => h j 0 i⟩

theorem neg_one_zpow_sum {ι : Type} (s : Finset ι) (m : ι → ℤ) : (-1 : ℂ) ^ (∑ i ∈ s, m i) = ∏ i ∈ s, (-1 : ℂ) ^ m i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (by norm_num), ih]

theorem al_prod {ι : Type} [Fintype ι] {N N' M M' : ℕ} (x : TaylorLogMetric.VC D N N') (y : ι → TaylorLogMetric.VC D M M')
    (hf : TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x x = ∑ i, TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) (y i) (y i))
    (hq : ∀ i, ∃ m : ℤ, Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) (y i) (y i)).re = (m : ℝ)) :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x = ∏ i, TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (y i) := by
  choose m hm using hq
  have h : Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x x).re = ((∑ i, m i : ℤ) : ℝ) := by
    rw [hf, Complex.re_sum, Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun i _ => hm i
  unfold TaylorLogMetric.al
  rw [h, round_intCast, neg_one_zpow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hm i, round_intCast]

theorem al_row (hS : B.StdOK) (N N' : ℕ) (x : TaylorLogMetric.VC D N N') (hx : x ∈ La0 B N N') :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x = ∏ i, TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (rowE D N N' x i) :=
  al_prod x _ (form_row _ N N' x x) fun i => B.qInt0 hS N 1 _ ((lat_row B N N' x).1 hx i)

theorem al_col (hS : B.StdOK) (N N' : ℕ) (x : TaylorLogMetric.VC D N N') (hx : x ∈ La0 B N N') :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x = ∏ j, TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (colE D N N' x j) :=
  al_prod x _ (form_col _ N N' x x) fun j => B.qInt0 hS N' 1 _ ((lat_col B N N' x).1 hx j)

end Formalism.L2.PairingIndexBounds.Eq.J
end
end

-- bundled from Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.NormOne
section
noncomputable section
open Classical Polynomial

namespace Formalism.L2.PairingIndexBounds.Eq.J

section Abstract

variable {E : Type} [Field E] [CharZero E] [StarRing E]

theorem one_add_ne (s : E) (hs : star s = -s) (t : ℕ) : (1 : E) + t * s ≠ 0 := by
  intro h
  have h2 : (1 : E) - t * s = 0 := by
    have := congrArg star h
    simpa [hs, sub_eq_add_neg] using this
  have h3 : (2 : E) = 0 := by linear_combination h + h2
  exact two_ne_zero h3

theorem one_sub_ne (s : E) (hs : star s = -s) (t : ℕ) : (1 : E) - t * s ≠ 0 := by
  have := one_add_ne (-s) (by rw [star_neg, hs]) t
  simpa [sub_eq_add_neg] using this

def cay (s : E) (t : ℕ) : E := (1 + t * s) / (1 - t * s)

theorem cay_norm (s : E) (hs : star s = -s) (t : ℕ) : star (cay s t) * cay s t = 1 := by
  have h1 := one_add_ne s hs t
  have h2 := one_sub_ne s hs t
  have : star (cay s t) = (1 - t * s) / (1 + t * s) := by
    unfold cay
    rw [star_div₀]
    simp [hs, sub_eq_add_neg]
  rw [this]
  unfold cay
  field_simp

theorem cay_inj (s : E) (hs : star s = -s) (hs0 : s ≠ 0) : Function.Injective (cay s) := by
  intro t u h
  unfold cay at h
  rw [div_eq_div_iff (one_sub_ne s hs t) (one_sub_ne s hs u)] at h
  have h2 : (2 : E) * s * ((t : E) - u) = 0 := by linear_combination h
  have h3 : (t : E) - u = 0 := by
    rcases mul_eq_zero.mp h2 with h4 | h4
    · exact absurd h4 (mul_ne_zero two_ne_zero hs0)
    · exact h4
  exact_mod_cast sub_eq_zero.mp h3

theorem exists_norm_one (s : E) (hs : star s = -s) (hs0 : s ≠ 0) (p : E[X]) (hp : p ≠ 0) :
    ∃ z : E, star z * z = 1 ∧ z ≠ 1 ∧ p.eval z ≠ 0 := by
  have hinf := Set.infinite_range_of_injective (cay_inj s hs hs0)
  obtain ⟨z, ⟨t, rfl⟩, hz⟩ := hinf.exists_notMem_finset (p.roots.toFinset ∪ {1})
  rw [Finset.mem_union, not_or, Multiset.mem_toFinset, Finset.mem_singleton, mem_roots hp] at hz
  exact ⟨_, cay_norm s hs t, hz.2, hz.1⟩

theorem eval_charpolyRev' {n : ℕ} (M : Matrix (Fin n) (Fin n) E) (z : E) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply, apply_ite]
  exact mul_comm _ _

theorem split_unitary (s : E) (hs : star s = -s) (hs0 : s ≠ 0) {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) E) :
    ∃ γ₁ γ₂ : Matrix.unitaryGroup (Fin n) E, γ = γ₁ * γ₂ ∧
      (1 - (γ₁ : Matrix (Fin n) (Fin n) E)).det ≠ 0 ∧ (1 - (γ₂ : Matrix (Fin n) (Fin n) E)).det ≠ 0 := by
  have hp : (γ : Matrix (Fin n) (Fin n) E).charpolyRev ≠ 0 := by
    intro h
    have := Matrix.eval_charpolyRev (M := (γ : Matrix (Fin n) (Fin n) E))
    rw [h] at this
    simp at this
  obtain ⟨z, hz, hz1, hzp⟩ := exists_norm_one s hs hs0 _ hp
  have hz' : z * star z = 1 := by rw [mul_comm]; exact hz
  have hu : (γ : Matrix (Fin n) (Fin n) E) * star (γ : Matrix (Fin n) (Fin n) E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ.2
  have m1 : z • (γ : Matrix (Fin n) (Fin n) E) ∈ Matrix.unitaryGroup (Fin n) E := by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hu, hz', one_smul]
  have m2 : star z • (1 : Matrix (Fin n) (Fin n) E) ∈ Matrix.unitaryGroup (Fin n) E := by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_star, star_one,
      Matrix.mul_one, hz, one_smul]
  refine ⟨⟨_, m1⟩, ⟨_, m2⟩, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show (γ : Matrix (Fin n) (Fin n) E) = z • (γ : Matrix (Fin n) (Fin n) E) * star z • (1 : Matrix (Fin n) (Fin n) E)
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one, hz', one_smul]
  · show (1 - z • (γ : Matrix (Fin n) (Fin n) E)).det ≠ 0
    rw [← eval_charpolyRev']; exact hzp
  · show (1 - star z • (1 : Matrix (Fin n) (Fin n) E)).det ≠ 0
    have : (1 - star z • (1 : Matrix (Fin n) (Fin n) E)) = (1 - star z) • (1 : Matrix (Fin n) (Fin n) E) := by
      rw [sub_smul, one_smul]
    rw [this, Matrix.det_smul, Matrix.det_one, mul_one]
    refine pow_ne_zero _ (sub_ne_zero.mpr fun h => hz1 ?_)
    have := congrArg star h
    rw [star_one, star_star] at this
    exact this.symm

end Abstract

open Formalism.BasicNotions Formalism.MainNotions NumberField

theorem exists_skew (D : D7) : letI := D.host.cmStar; ∃ s : D.host.E, star s = -s ∧ s ≠ 0 := by
  letI := D.host.cmStar
  haveI := D.host.isCMField_hostE
  by_contra hno
  push Not at hno
  apply NumberField.IsCMField.complexConj_ne_one D.host.E
  refine AlgEquiv.ext fun x => ?_
  have h := hno (x - star x) (by rw [star_sub, star_star]; ring)
  exact (sub_eq_zero.mp h).symm

theorem split_host (D : D7) {n : ℕ} :
    letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E,
    ∃ γ₁ γ₂ : Matrix.unitaryGroup (Fin n) D.host.E, γ = γ₁ * γ₂ ∧
      (1 - (γ₁ : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0 ∧ (1 - (γ₂ : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0 := by
  letI := D.host.cmStar
  intro γ
  obtain ⟨s, hs, hs0⟩ := exists_skew D
  exact split_unitary s hs hs0 γ

end Formalism.L2.PairingIndexBounds.Eq.J
end
end

