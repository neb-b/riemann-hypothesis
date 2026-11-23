module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ArchimedeanLocalHeightTerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0033

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteLocalHeightTerm
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

theorem finite_local_height_term (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N) (κ : K) (hκ : κ ≠ 0)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c)
    (hFne : F ≠ 0) (hFx : d.translatedForm x F ≠ 0) (hs : d.heightSubstitutionCondition h x c F κ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    d.localHeightAtPrime h (d.wx x) c la * logNorm la =
      Real.log (gaussAbs (FinitePlace.mk la) F) -
        Real.log (gaussAbs (FinitePlace.mk la) (d.translatedForm x F)) +
        Real.log (FinitePlace.mk la κ) := by
  let : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  set ra := ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) with hra
  have hmem := d.linearCombination_mem_section hd x c
  have hra0 : ra ≠ 0 := d.ratio_base_ne_zero hd c hmem (hx c)

  obtain ⟨κ3, hκ3, hN⟩ := (d.norm_factorization hd h).1 c ra hra0
  obtain ⟨a1, b1, ha1, hb1, hsplit1⟩ := d.hint_good_split hd h c _
    (fun p _ hp => d.hint_good_of_ne c p hp)
  rw [hsplit1] at hN
  have hraS : algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (Ω c) _).injective).2 hra0
  have hNm0 : Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hraS).map (Algebra.norm (KTf K d.D d.N))).ne_zero
  have hb10 : b1 ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, mul_zero] at hN
    exact hNm0 hN
  have ha10 : a1 ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, mul_zero] at hN
    exact hNm0 hN
  set a1' : KTp K d.D d.N := MvPolynomial.C κ3 * a1 with ha1'
  have hkey1 : Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra) *
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a1' := by
    have hbne : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 hb10
    rw [hN, ha1', map_mul, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    field_simp

  obtain ⟨F', hF', hF'0, hFmh, -, -⟩ := d.componentForm_properties hd h c
  have hFF : F' = F := hinj (hF'.trans hF.symm)
  subst hFF
  obtain ⟨a2, b2, ha2, hb2, hsplit2⟩ := d.hint_good_split hd h c
    (fun p => d.nPMM h c (d.w (d.jc c) c) p)
    (fun p _ hp => d.hint_good_of_ne c p
      (f := fun w => (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c)) hp)
  have hfZ : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F' =
      Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2 /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b2) := by
    rw [hF, ← hsplit2]; rfl
  have hb20 : b2 ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, mul_zero, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))]
      at hfZ
    exact hFne (hinj hfZ)
  have ha20 : a2 ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, mul_zero, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))]
      at hfZ
    exact hFne (hinj hfZ)
  have hkey2 : Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2 =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F' * b2) := by
    have hbne : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b2 ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 hb20
    rw [map_mul, hfZ]
    field_simp

  have hpoly : MvPolynomial.C κ * a1' * a2 = d.translatedForm x F' * b2 * b1 := by
    apply mul_left_cancel₀ hFne
    apply hinj
    have hs' := hs
    unfold heightSubstitutionCondition at hs'
    rw [map_mul] at hkey2
    have hCk : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C κ) =
        algebraMap K (KTf K d.D d.N) κ := by
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    simp only [map_mul, hCk]
    linear_combination (-(algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F' *
        algebraMap K (KTf K d.D d.N) κ * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2)) * hkey1 +
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2) * hs' +
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.translatedForm x F') *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1) * hkey2

  have hfin := (d.places_over_la hd h la c).1
  have hZ : ∀ w ∈ d.PlOver la c, d.ordMM c (d.Wres c w) (d.wx x c) =
      (w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra)).untopD 0 - (w (d.rationalBaseRow c)).untopD 0 := by
    intro w hw
    obtain ⟨hv, -, j0, hj0, hint, hunit⟩ := d.admissible_over_prime hd h la c w hw
    exact d.ordMinMax_at_good_place hd c w hv j0 hj0 hint hunit hmem (hx c)
  have hNla : d.localHeightAtPrime h (d.wx x) c la =
      (d.nLa h c la (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra) : ℝ) - (d.nLa h c la (d.rationalBaseRow c) : ℝ) := by
    unfold localHeightAtPrime nLa
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
      finsum_mem_eq_finite_toFinset_sum _ hfin]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hZ w (hfin.mem_toFinset.1 hw)]; push_cast; ring

  have ha1'0 : a1' ≠ 0 := mul_ne_zero (by simpa using hκ3) ha10
  have hw0 : d.rationalBaseRow c ≠ 0 := d.lineRatio_ne_zero hd c
  have p1 := d.pf_fin hd h c _ hraS a1' b1 ha1'0 hb10 hkey1 la
  have p2 := d.pf_fin hd h c _ hw0 (F' * b2) a2 (mul_ne_zero hFne hb20) ha20 hkey2 la

  set v := FinitePlace.mk la with hv
  have hg := congrArg (gaussAbs v) hpoly
  rw [gauss_abs_mul v _ _ (mul_ne_zero (by simpa using hκ) ha1'0) ha20,
    gauss_abs_mul v _ _ (by simpa using hκ) ha1'0, HeightMultiplicativity.gaussAbs_C,
    gauss_abs_mul v _ _ (mul_ne_zero hFx hb20) hb10,
    gauss_abs_mul v _ _ hFx hb20] at hg
  have hl := congrArg Real.log hg
  have hk0 : 0 < v κ := (FinitePlace.pos_iff).2 hκ
  have q1 := gauss_abs_pos_of_ne_zero v a1' ha1'0
  have q2 := gauss_abs_pos_of_ne_zero v a2 ha20
  have q3 := gauss_abs_pos_of_ne_zero v _ hFx
  have q4 := gauss_abs_pos_of_ne_zero v b2 hb20
  have q5 := gauss_abs_pos_of_ne_zero v b1 hb10
  have q6 := gauss_abs_pos_of_ne_zero v F' hFne
  rw [Real.log_mul (by positivity) q2.ne', Real.log_mul hk0.ne' q1.ne',
    Real.log_mul (by positivity) q5.ne', Real.log_mul q3.ne' q4.ne'] at hl
  rw [gauss_abs_mul v _ _ hFne hb20, Real.log_mul q6.ne' q4.ne'] at p2
  rw [hNla]
  linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.PolyL2EqSqrtCoeffSum
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

def hupsWx (D N : ℕ) : UXVar D N → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

def hupsWu (D N : ℕ) : UXVar D N → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)

theorem hups_xDeg_eq {D N : ℕ} (s : UXVar D N →₀ ℕ) : xDeg s = hupsWt (hupsWx D N) s := by
  unfold hupsWt xDeg
  rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type]
  simp [hupsWx]

theorem hups_uDeg_eq {D N : ℕ} (s : UXVar D N →₀ ℕ) : uDeg s = hupsWt (hupsWu D N) s := by
  unfold hupsWt uDeg
  rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type]
  simp [hupsWu]

theorem hups_xDeg_add {D N : ℕ} (s t : UXVar D N →₀ ℕ) : xDeg (s + t) = xDeg s + xDeg t := by
  unfold xDeg; simp [Finset.sum_add_distrib]

theorem hups_uDeg_add {D N : ℕ} (s t : UXVar D N →₀ ℕ) : uDeg (s + t) = uDeg s + uDeg t := by
  unfold uDeg; simp [Finset.sum_add_distrib]

theorem hups_cofactor {R : Type*} [CommRing R] [IsDomain R] {D N : ℕ}
    {F P : MvPolynomial (UXVar D N) R} (hF : F ≠ 0) {deF u n n' : ℕ} (hFx : XHom deF F)
    {sF : UXVar D N →₀ ℕ} (hsF : sF ∈ F.support) (hsFu : uDeg sF = u)
    (hx : XHom n (F * P)) (hu : UDegLE n' (F * P)) :
    ∀ s ∈ P.support, s ∈ upMono D N (n - deF) (n' - u) := by
  intro s hs
  rw [mem_upMono]
  have h1 := hups_hom_of_mul (hupsWx D N) hF (a := deF) (n := n)
    (fun t ht => (hups_xDeg_eq t).symm.trans (hFx t ht))
    (fun t ht => (hups_xDeg_eq t).symm.trans (hx t ht)) hs
  have h2 := hups_deg_of_mul (hupsWu D N) (u := u) (n := n') hsF ((hups_uDeg_eq sF).symm.trans hsFu)
    (fun t ht => (hups_uDeg_eq t) ▸ hu t ht) hs
  rw [← hups_xDeg_eq] at h1
  rw [← hups_uDeg_eq] at h2
  omega

theorem hups_span_transfer {K : Type} [Field K] (σ : K →+* ℂ) {α β : Type} [Fintype α] [Fintype β]
    {r : ℕ} (u : α → Fin r → K) (v : β → Fin r → K)
    (h : ∀ a, u a ∈ Submodule.span K (Set.range v)) (z : α → ℂ) :
    ∃ y : β → ℂ, ∀ i, ∑ a, z a * σ (u a i) = ∑ b, y b * σ (v b i) := by
  choose c hc using fun a => (Submodule.mem_span_range_iff_exists_fun K).1 (h a)
  refine ⟨fun b => ∑ a, z a * σ (c a b), fun i => ?_⟩
  have hu : ∀ a, u a i = ∑ b, c a b * v b i := fun a => by
    rw [← hc a, Finset.sum_apply]; simp [smul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hu, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

theorem hups_coeff_mul_of_supp {σ R : Type*} [CommRing R] (F P : MvPolynomial σ R)
    (S : Finset (σ →₀ ℕ)) (hP : P.support ⊆ S) (t : σ →₀ ℕ) :
    (F * P).coeff t = ∑ m : S, P.coeff m * (F * MvPolynomial.monomial (m : σ →₀ ℕ) 1).coeff t := by
  classical
  have hPs : P = ∑ m ∈ S, MvPolynomial.monomial m (P.coeff m) := by
    conv_lhs => rw [P.as_sum]
    exact Finset.sum_subset hP fun m _ hm => by simp [MvPolynomial.notMem_support_iff.1 hm]
  conv_lhs => rw [hPs]
  rw [Finset.mul_sum, MvPolynomial.coeff_sum, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show MvPolynomial.monomial (m : σ →₀ ℕ) (P.coeff m) =
      MvPolynomial.C (P.coeff m) * MvPolynomial.monomial (m : σ →₀ ℕ) 1 by
    rw [MvPolynomial.C_mul_monomial, mul_one]]
  rw [mul_left_comm, MvPolynomial.coeff_C_mul]

theorem polyL2_eq_sqrt_coeff_sum {σ : Type*} (f : MvPolynomial σ ℂ) (V : Finset (σ →₀ ℕ)) {r : ℕ}
    (e : V ≃ Fin r) (hf : f.support ⊆ V) :
    ReciprocityTheory.MultiplicativeHeights.polyL2 f = Real.sqrt (∑ i, ‖f.coeff (e.symm i : σ →₀ ℕ)‖ ^ 2) := by
  unfold ReciprocityTheory.MultiplicativeHeights.polyL2
  congr 1
  rw [Finset.sum_subset hf fun s _ hs => by simp [MvPolynomial.notMem_support_iff.1 hs],
    ← Finset.sum_coe_sort V]
  exact (Equiv.sum_comp e.symm (fun x : V => ‖f.coeff (x : σ →₀ ℕ)‖ ^ 2)).symm

theorem hups_choose_strict (D : ℕ) : StrictMono fun m : ℕ => (m + D + 1).choose (D + 1) := by
  refine strictMono_nat_of_lt_succ fun m => ?_
  show (m + D + 1).choose (D + 1) < (m + 1 + D + 1).choose (D + 1)
  rw [show m + 1 + D + 1 = (m + D + 1) + 1 by omega, Nat.choose_succ_succ' (m + D + 1) D]
  have := Nat.choose_pos (show D ≤ m + D + 1 by omega)
  omega

theorem hups_cardUX_lt (D N n n' deF u : ℕ) (h1 : 1 ≤ deF) (hn : deF ≤ n) :
    cardUX D N (n - deF) (n' - u) < cardUX D N n n' := by
  unfold cardUX
  have ha : (n - deF + D + 1).choose (D + 1) < (n + D + 1).choose (D + 1) :=
    hups_choose_strict D (show n - deF < n by omega)
  have hb : (n' - u + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) ≤
      (n' + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) :=
    Nat.choose_le_choose _ (by omega)
  have hb0 : 0 < (n' - u + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) :=
    Nat.choose_pos (by omega)
  calc _ < (n + D + 1).choose (D + 1) * (n' - u + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) :=
        Nat.mul_lt_mul_of_pos_right ha hb0
    _ ≤ _ := Nat.mul_le_mul_left _ hb

theorem hups_log_rd_nonneg (K : Type) [Field K] [NumberField K] :
    0 ≤ Real.log (|(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ))) := by
  apply Real.log_nonneg
  apply Real.one_le_rpow _ (by positivity)
  have h := NumberField.discr_ne_zero K
  have : (1 : ℤ) ≤ |NumberField.discr K| := Int.one_le_abs h
  have : ((1 : ℤ) : ℝ) ≤ ((|NumberField.discr K| : ℤ) : ℝ) := by exact_mod_cast this
  simpa [Int.cast_abs] using this

theorem polyL2_nonneg {σ : Type*} (f : MvPolynomial σ ℂ) : 0 ≤ ReciprocityTheory.MultiplicativeHeights.polyL2 f := by
  unfold ReciprocityTheory.MultiplicativeHeights.polyL2; exact Real.sqrt_nonneg _

theorem hups_qnorm_eq {K : Type} [Field K] [NumberField K] {D N : ℕ} (σ : K →+* ℂ)
    (F1 : MvPolynomial (UXVar D N) K) {n n' : ℕ} (V S : Finset (UXVar D N →₀ ℕ))
    (hVd : ∀ s ∈ V, xDeg s = n ∧ uDeg s ≤ n')
    (hadd : ∀ a ∈ F1.support, ∀ m ∈ S, a + m ∈ V)
    (hcof : ∀ P : MvPolynomial (UXVar D N) ℂ, XHom n (MvPolynomial.map σ F1 * P) →
      UDegLE n' (MvPolynomial.map σ F1 * P) → P.support ⊆ S)
    {r k : ℕ} (e : V ≃ Fin r) (b : Fin k → Fin r → K)
    (hspan : Submodule.span K (Set.range b) =
      Submodule.span K (Set.range fun m : S =>
        fun i => (F1 * MvPolynomial.monomial (m : UXVar D N →₀ ℕ) 1).coeff
          (e.symm i : UXVar D N →₀ ℕ)))
    (Q : MvPolynomial (UXVar D N) (𝓞 K)) (hQsupp : Q.support ⊆ V) :
    qnorm σ F1 n n' Q = qdist σ b (fun i => ((Q.coeff (e.symm i : UXVar D N →₀ ℕ) : 𝓞 K) : K)) := by
  classical
  unfold qnorm qdist
  beta_reduce
  have hc : ∀ m : S, (fun i => (F1 * MvPolynomial.monomial (m : UXVar D N →₀ ℕ) 1).coeff
      (e.symm i : UXVar D N →₀ ℕ)) ∈ Submodule.span K (Set.range b) := fun m => by
    rw [hspan]; exact Submodule.subset_span ⟨m, rfl⟩
  have hbc : ∀ j, b j ∈ Submodule.span K (Set.range fun m : S =>
      fun i => (F1 * MvPolynomial.monomial (m : UXVar D N →₀ ℕ) 1).coeff
        (e.symm i : UXVar D N →₀ ℕ)) := fun j => by
    rw [← hspan]; exact Submodule.subset_span ⟨j, rfl⟩
  generalize hcdef : (fun m : S => fun i => (F1 * MvPolynomial.monomial (m : UXVar D N →₀ ℕ) 1).coeff
      (e.symm i : UXVar D N →₀ ℕ)) = c at hc hbc
  have hcv : ∀ (m : S) i, c m i = (F1 * MvPolynomial.monomial (m : UXVar D N →₀ ℕ) 1).coeff
      (e.symm i : UXVar D N →₀ ℕ) := fun m i => by rw [← hcdef]
  have hFσs : (MvPolynomial.map σ F1).support = F1.support :=
    MvPolynomial.support_map_of_injective _ σ.injective
  generalize hFσ : MvPolynomial.map σ F1 = Fσ at hcof hFσs ⊢
  generalize hQσ : MvPolynomial.map (σ.comp (algebraMap (𝓞 K) K)) Q = Qσ
  have hQσs : Qσ.support ⊆ V := hQσ ▸ (MvPolynomial.support_map_subset _ _).trans hQsupp
  have hQσc : ∀ i, Qσ.coeff (e.symm i : UXVar D N →₀ ℕ) =
      σ ((Q.coeff (e.symm i : UXVar D N →₀ ℕ) : 𝓞 K) : K) := fun i => by
    rw [← hQσ, MvPolynomial.coeff_map]; rfl
  have hcσ : ∀ (m : S) i, (Fσ * MvPolynomial.monomial (m : UXVar D N →₀ ℕ) 1).coeff
      (e.symm i : UXVar D N →₀ ℕ) = σ (c m i) := by
    intro m i
    rw [hcv, ← hFσ, show (1 : ℂ) = σ 1 from σ.map_one.symm, ← MvPolynomial.map_monomial, ← map_mul,
      MvPolynomial.coeff_map]
  have hmulV : ∀ P : MvPolynomial (UXVar D N) ℂ, P.support ⊆ S → (Fσ * P).support ⊆ V := by
    intro P hP s hs
    obtain ⟨a, ha, m, hm, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul Fσ P hs)
    exact hadd a (hFσs ▸ ha) m (hP hm)
  have hval : ∀ P : MvPolynomial (UXVar D N) ℂ, P.support ⊆ S →
      ReciprocityTheory.MultiplicativeHeights.polyL2 (Qσ + Fσ * P) =
        Real.sqrt (∑ i, ‖σ ((Q.coeff (e.symm i : UXVar D N →₀ ℕ) : 𝓞 K) : K) +
          ∑ m : S, P.coeff m * σ (c m i)‖ ^ 2) := by
    intro P hP
    rw [polyL2_eq_sqrt_coeff_sum _ V e (MvPolynomial.support_add.trans (Finset.union_subset hQσs (hmulV P hP)))]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.coeff_add, hQσc, hups_coeff_mul_of_supp Fσ P S hP]
    simp only [hcσ]
  have hbdd1 : BddBelow (Set.range fun P : {P : MvPolynomial (UXVar D N) ℂ //
      XHom n (Fσ * P) ∧ UDegLE n' (Fσ * P)} => ReciprocityTheory.MultiplicativeHeights.polyL2 (Qσ + Fσ * P.1)) :=
    ⟨0, by rintro _ ⟨P, rfl⟩; exact polyL2_nonneg _⟩
  have hbdd2 : BddBelow (Set.range fun z : Fin k → ℂ =>
      Real.sqrt (∑ i, ‖σ ((Q.coeff (e.symm i : UXVar D N →₀ ℕ) : 𝓞 K) : K) +
        ∑ j, z j * σ (b j i)‖ ^ 2)) :=
    ⟨0, by rintro _ ⟨z, rfl⟩; exact Real.sqrt_nonneg _⟩
  apply le_antisymm
  · apply le_ciInf
    intro z
    obtain ⟨y, hy⟩ := hups_span_transfer σ b c hbc z
    obtain ⟨P, hP⟩ : ∃ P : MvPolynomial (UXVar D N) ℂ,
        P = ∑ m : S, MvPolynomial.monomial (m : UXVar D N →₀ ℕ) (y m) := ⟨_, rfl⟩
    have hPc : ∀ m : S, P.coeff m = y m := fun m => by
      rw [hP, MvPolynomial.coeff_sum, Fintype.sum_eq_single m]
      · simp
      · intro m' hm'
        rw [MvPolynomial.coeff_monomial, if_neg]
        exact fun h => hm' (Subtype.ext h)
    have hPS : P.support ⊆ S := by
      intro s hs
      by_contra h
      rw [MvPolynomial.mem_support_iff, hP, MvPolynomial.coeff_sum] at hs
      apply hs
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [MvPolynomial.coeff_monomial, if_neg]
      exact fun h' => h (h' ▸ m.2)
    have hPV := hmulV P hPS
    have hadm : XHom n (Fσ * P) ∧ UDegLE n' (Fσ * P) :=
      ⟨fun s hs => (hVd s (hPV hs)).1, fun s hs => (hVd s (hPV hs)).2⟩
    refine (ciInf_le hbdd1 ⟨P, hadm⟩).trans (le_of_eq ?_)
    show ReciprocityTheory.MultiplicativeHeights.polyL2 (Qσ + Fσ * P) = _
    rw [hval P hPS]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hy i]
    simp only [hPc]
  · have : Nonempty {P : MvPolynomial (UXVar D N) ℂ // XHom n (Fσ * P) ∧ UDegLE n' (Fσ * P)} :=
      ⟨⟨0, by simp [XHom], by simp [UDegLE]⟩⟩
    apply le_ciInf
    rintro ⟨P, hPx, hPu⟩
    have hPS : P.support ⊆ S := hcof P hPx hPu
    obtain ⟨z, hz⟩ := hups_span_transfer σ c b (fun m => by rw [← hcdef]; exact hc m) (fun m => P.coeff m)
    refine (ciInf_le hbdd2 z).trans (le_of_eq ?_)
    show _ = ReciprocityTheory.MultiplicativeHeights.polyL2 (Qσ + Fσ * P)
    rw [hval P hPS]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz i]

end ReciprocityTheory.ChartRestriction.G.T0
end

