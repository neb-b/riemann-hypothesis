module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.CosetIntegral
section
open MeasureTheory GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertZeta

theorem cosetIntegral : CosetIntegral := by
  intro G _ _ _ _ _ μ _ K hK hμK F Z hF hZ
  set f : G ⧸ K → ℂ := fun x => F x.out with hf_def
  have hFf : ∀ g, F g = f (QuotientGroup.mk g) := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K g
    simp only [hf_def, hh, hF g h h.2]
  set C : G ⧸ K → Set G := fun x => (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {x} with hC_def
  have hC_eq : ∀ x, C x = (fun h => x.out⁻¹ * h) ⁻¹' (K : Set G) := by
    intro x
    ext g
    simp only [hC_def, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    conv_lhs => rw [← QuotientGroup.out_eq' x]
    rw [eq_comm, QuotientGroup.eq]
  have hC_open : ∀ x, IsOpen (C x) := fun x => by
    rw [hC_eq]
    exact hK.preimage (continuous_const_mul _)
  have hC_meas : ∀ x, MeasurableSet (C x) := fun x => (hC_open x).measurableSet
  have hC_one : ∀ x, μ (C x) = 1 := fun x => by
    rw [hC_eq, measure_preimage_mul, hμK]
  have hF_on : ∀ x, Set.EqOn F (fun _ => f x) (C x) := by
    intro x g hg
    simp only [hC_def, Set.mem_preimage, Set.mem_singleton_iff] at hg
    rw [hFf g, hg]
  have hcount : (Function.support f).Countable := hZ.summable.countable_support
  have : Countable (Function.support f) := hcount.to_subtype
  set s : Function.support f → Set G := fun i => C i with hs_def
  have hs_meas : ∀ i, MeasurableSet (s i) := fun i => hC_meas _
  have hs_disj : Pairwise (Function.onFun Disjoint s) := by
    intro i j hij
    refine Disjoint.preimage _ (Set.disjoint_singleton.2 fun h => hij (Subtype.ext h))
  have hs_int : ∀ i, IntegrableOn F (s i) μ := by
    intro i
    refine (integrableOn_const (by rw [hC_one]; exact ENNReal.one_ne_top)).congr_fun
      (fun g hg => (hF_on i hg).symm) (hs_meas i)
  have hs_val : ∀ i, ∫ g in s i, F g ∂μ = f i := by
    intro i
    rw [setIntegral_congr_fun (hs_meas i) (hF_on i), setIntegral_const]
    simp [Measure.real, hs_def, hC_one]
  have hs_norm : ∀ i, ∫ g in s i, ‖F g‖ ∂μ = ‖f i‖ := by
    intro i
    rw [setIntegral_congr_fun (hs_meas i) (fun g hg => congrArg norm (hF_on i hg)), setIntegral_const]
    simp [Measure.real, hs_def, hC_one]
  have hU : IntegrableOn F (⋃ i, s i) μ := by
    refine integrableOn_iUnion_of_summable_integral_norm hs_int ?_
    simp only [hs_norm]
    exact hZ.summable.norm.subtype _
  have hout : ∀ g, g ∉ ⋃ i, s i → F g = 0 := by
    intro g hg
    by_contra hne
    apply hg
    have hmem : QuotientGroup.mk g ∈ Function.support f := by
      rw [Function.mem_support, ← hFf g]
      exact hne
    exact Set.mem_iUnion.2 ⟨⟨_, hmem⟩, rfl⟩
  have hint : Integrable F μ := hU.integrable_of_forall_notMem_eq_zero hout
  refine ⟨hint, ?_⟩
  have hsum := hasSum_integral_iUnion hs_meas hs_disj hU
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout] at hsum
  simp only [hs_val] at hsum
  exact (hasSum_subtype_support.1 hsum).unique hZ

end GlobalTheory.CompanionTheory.InertZeta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.DoubleCosetSwap
section
noncomputable section

open Formalism.UG GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertZeta

variable {G : Type} [Group G] {K : Subgroup G}

def cosetsIn (hK : IsCommensurated K) (g : G) : Finset (G ⧸ K) :=
  (P.finite_cosets_in_doset hK g).toFinset

theorem mem_cosetsIn {hK : IsCommensurated K} {g : G} {x : G ⧸ K} :
    x ∈ cosetsIn hK g ↔ x.out ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by
  rw [cosetsIn, Set.Finite.mem_toFinset, DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, a.2, b, b.2, h⟩
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩

theorem hAct_dosetInd (hK : IsCommensurated K) (g : G) (f : G → ℂ) :
    hAct K (dosetInd ℂ K g) f 1 = ∑ x ∈ cosetsIn hK g, f x.out := by
  unfold hAct
  rw [finsum_eq_sum_of_support_subset (s := cosetsIn hK g)]
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hm : x.out ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := mem_cosetsIn.mp hx
    simp [dosetInd, Set.indicator_apply, hm]
  · intro x hx
    rw [Function.mem_support] at hx
    rw [Finset.mem_coe, mem_cosetsIn]
    by_contra hm
    apply hx
    simp [dosetInd, Set.indicator_apply, hm]

theorem eq_of_mem_cosetsIn {hK : IsCommensurated K} {f : G → ℂ} (hf : IsBiInv K f) {g : G} {x : G ⧸ K}
    (hx : x ∈ cosetsIn hK g) : f x.out = f g := by
  obtain ⟨a, ha, b, hb, h⟩ := DoubleCoset.mem_doubleCoset.mp (mem_cosetsIn.mp hx)
  rw [h]
  exact hf ⟨a, ha⟩ ⟨b, hb⟩ g

def dosetOf (x : G ⧸ K) : Set G := DoubleCoset.doubleCoset x.out (K : Set G) (K : Set G)

theorem dosetOf_eq_iff {hK : IsCommensurated K} {x y : G ⧸ K} : dosetOf y = dosetOf x ↔ y ∈ cosetsIn hK x.out := by
  rw [mem_cosetsIn]
  unfold dosetOf
  constructor
  · intro h
    rw [← h]
    exact DoubleCoset.mem_doubleCoset_self K K y.out
  · intro h
    exact DoubleCoset.doubleCoset_eq_of_mem h

theorem tsum_fiber {M : Type} [AddCommMonoid M] [TopologicalSpace M] (hK : IsCommensurated K) (x : G ⧸ K)
    (h : G ⧸ K → M) : ∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, h c = ∑ y ∈ cosetsIn hK x.out, h y := by
  rw [← Finset.tsum_subtype (cosetsIn hK x.out) h]
  exact (Equiv.subtypeEquivRight
    (fun y => (dosetOf_eq_iff (hK := hK) (x := x) (y := y)))).tsum_eq (fun c => h c.1)

theorem finite_fiber (hK : IsCommensurated K) (q : Set G) : Finite {y : G ⧸ K // dosetOf y = q} := by
  by_cases hne : ∃ y : G ⧸ K, dosetOf y = q
  · obtain ⟨x, rfl⟩ := hne
    exact Finite.of_equiv _ (Equiv.subtypeEquivRight
      (fun y => (dosetOf_eq_iff (hK := hK) (x := x) (y := y)))).symm
  · haveI : IsEmpty {y : G ⧸ K // dosetOf y = q} := ⟨fun c => hne ⟨c.1, c.2⟩⟩
    infer_instance

theorem fiber_compare (hK : IsCommensurated K) {F w φ : G → ℂ} (hF : IsBiInv K F) (hw : IsBiInv K w)
    (h : ∀ g, hAct K (dosetInd ℂ K g) w 1 = hAct K (dosetInd ℂ K g) φ 1) (q : Set G) :
    ∑' c : {y : G ⧸ K // dosetOf y = q}, F c.1.out * φ c.1.out = ∑' c : {y : G ⧸ K // dosetOf y = q}, F c.1.out * w c.1.out ∧
    ∑' c : {y : G ⧸ K // dosetOf y = q}, ‖F c.1.out * w c.1.out‖ ≤
      ∑' c : {y : G ⧸ K // dosetOf y = q}, ‖F c.1.out * φ c.1.out‖ := by
  by_cases hne : ∃ y : G ⧸ K, dosetOf y = q
  · obtain ⟨x, rfl⟩ := hne
    have t1 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, F c.1.out * φ c.1.out) =
        ∑ y ∈ cosetsIn hK x.out, F y.out * φ y.out := tsum_fiber hK x (fun y => F y.out * φ y.out)
    have t2 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, F c.1.out * w c.1.out) =
        ∑ y ∈ cosetsIn hK x.out, F y.out * w y.out := tsum_fiber hK x (fun y => F y.out * w y.out)
    have t3 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, ‖F c.1.out * w c.1.out‖) =
        ∑ y ∈ cosetsIn hK x.out, ‖F y.out * w y.out‖ := tsum_fiber hK x (fun y => ‖F y.out * w y.out‖)
    have t4 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, ‖F c.1.out * φ c.1.out‖) =
        ∑ y ∈ cosetsIn hK x.out, ‖F y.out * φ y.out‖ := tsum_fiber hK x (fun y => ‖F y.out * φ y.out‖)
    rw [t1, t2, t3, t4]
    have hF' : ∀ y ∈ cosetsIn hK x.out, F y.out = F x.out := fun y hy => eq_of_mem_cosetsIn hF hy
    have hW' : ∀ y ∈ cosetsIn hK x.out, w y.out = w x.out := fun y hy => eq_of_mem_cosetsIn hw hy
    have hsum : ∑ y ∈ cosetsIn hK x.out, φ y.out = ∑ y ∈ cosetsIn hK x.out, w y.out := by
      rw [← hAct_dosetInd hK, ← hAct_dosetInd hK, h]
    have e1 : ∑ y ∈ cosetsIn hK x.out, F y.out * φ y.out = F x.out * ∑ y ∈ cosetsIn hK x.out, φ y.out := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y hy => by rw [hF' y hy]
    have e2 : ∑ y ∈ cosetsIn hK x.out, F y.out * w y.out = F x.out * ∑ y ∈ cosetsIn hK x.out, w y.out := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y hy => by rw [hF' y hy]
    have e4 : ∑ y ∈ cosetsIn hK x.out, F y.out * w y.out = ∑ y ∈ cosetsIn hK x.out, F y.out * φ y.out := by
      rw [e1, e2, hsum]
    have hc : ∀ y ∈ cosetsIn hK x.out, F y.out * w y.out = F x.out * w x.out := fun y hy => by
      rw [hF' y hy, hW' y hy]
    have e3 : ∑ y ∈ cosetsIn hK x.out, ‖F y.out * w y.out‖ = ‖∑ y ∈ cosetsIn hK x.out, F y.out * w y.out‖ := by
      rw [Finset.sum_congr rfl hc, Finset.sum_congr rfl (fun y hy => congrArg (‖·‖) (hc y hy))]
      simp only [Finset.sum_const, nsmul_eq_mul, norm_mul, Complex.norm_natCast]
    refine ⟨e4.symm, ?_⟩
    rw [e3, e4]
    exact norm_sum_le _ _
  · haveI : IsEmpty {y : G ⧸ K // dosetOf y = q} := ⟨fun c => hne ⟨c.1, c.2⟩⟩
    simp only [tsum_empty, le_refl, and_self]

theorem dosetSwap : DosetSwap := by
  intro G _ K hK F w φ Z hF hw h ha
  let e : (Σ q : Set G, {y : G ⧸ K // dosetOf y = q}) ≃ G ⧸ K := Equiv.sigmaFiberEquiv dosetOf
  have haN : Summable fun x : G ⧸ K => ‖F x.out * φ x.out‖ := summable_norm_iff.mpr ha.summable
  have haN' : Summable fun p => ‖F (e p).out * φ (e p).out‖ :=
    (e.summable_iff (f := fun x : G ⧸ K => ‖F x.out * φ x.out‖)).mpr haN
  have hbN' : Summable fun p => ‖F (e p).out * w (e p).out‖ := by
    rw [summable_sigma_of_nonneg (fun p => norm_nonneg _)]
    refine ⟨fun q => ?_, ?_⟩
    · haveI := finite_fiber hK q
      exact Summable.of_finite
    · have hA := ((summable_sigma_of_nonneg (fun p => norm_nonneg _)).mp haN').2
      refine Summable.of_nonneg_of_le (fun q => tsum_nonneg fun _ => norm_nonneg _) (fun q => ?_) hA
      exact (fiber_compare hK hF hw h q).2
  have hbN : Summable fun x : G ⧸ K => ‖F x.out * w x.out‖ :=
    (e.summable_iff (f := fun x : G ⧸ K => ‖F x.out * w x.out‖)).mp hbN'
  have hbS : Summable fun x : G ⧸ K => F x.out * w x.out := hbN.of_norm
  have hbS' : Summable fun p => F (e p).out * w (e p).out :=
    (e.summable_iff (f := fun x : G ⧸ K => F x.out * w x.out)).mpr hbS
  have haS' : Summable fun p => F (e p).out * φ (e p).out :=
    (e.summable_iff (f := fun x : G ⧸ K => F x.out * φ x.out)).mpr ha.summable
  have key : ∑' x : G ⧸ K, F x.out * w x.out = ∑' x : G ⧸ K, F x.out * φ x.out := by
    calc ∑' x : G ⧸ K, F x.out * w x.out = ∑' p, F (e p).out * w (e p).out :=
          (e.tsum_eq (fun x => F x.out * w x.out)).symm
      _ = ∑' q, ∑' c : {y : G ⧸ K // dosetOf y = q}, F c.1.out * w c.1.out := hbS'.tsum_sigma
      _ = ∑' q, ∑' c : {y : G ⧸ K // dosetOf y = q}, F c.1.out * φ c.1.out :=
          tsum_congr fun q => ((fiber_compare hK hF hw h q).1).symm
      _ = ∑' p, F (e p).out * φ (e p).out := haS'.tsum_sigma.symm
      _ = ∑' x : G ⧸ K, F x.out * φ x.out := e.tsum_eq (fun x => F x.out * φ x.out)
  have hb := hbS.hasSum
  rwa [key, ha.tsum_eq] at hb

end GlobalTheory.CompanionTheory.InertZeta
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.DualPairingExists
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertDual

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}

theorem antiJ_iff (i j : Fin N) : i.val + j.val + 1 = N ↔ j = i.rev := by
  rw [Fin.ext_iff, Fin.val_rev]
  have := i.isLt
  have := j.isLt
  constructor <;> intro h <;> omega

theorem antiJ_mulVec (b : Fin N → L) (k : Fin N) : (antiJ L N *ᵥ b) k = b k.rev := by
  simp [Matrix.mulVec, dotProduct, antiJ, antiJ_iff]

theorem antiJ_mul_self : antiJ L N * antiJ L N = 1 := by
  ext i j
  simp only [Matrix.mul_apply, antiJ, antiJ_iff, boole_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Fin.rev_rev, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem isInt_antiJ : IsInt (antiJ L N) := by
  intro i j
  simp only [antiJ]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem cT_add (σ : L →+* L) (A B : Matrix (Fin N) (Fin N) L) : cT σ (A + B) = cT σ A + cT σ B := by
  ext i j
  simp [cT]

theorem isInt_cT {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {M : Matrix (Fin N) (Fin N) L} (hM : IsInt M) :
    IsInt (cT σ M) := by
  intro i j
  have h : M j i ∈ intL L := hM j i
  have hmem : ∀ x : L, x ∈ intL L ↔ Valued.v x ≤ 1 := fun x => Valuation.mem_integer_iff _ _
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  rw [hmem] at h ⊢
  rw [hσ]
  exact h

theorem int_mulVec {M : Matrix (Fin N) (Fin N) L} (hM : IsInt M) {w : Fin N → L} (hw : ∀ i, w i ∈ intL L) (i : Fin N) :
    (M *ᵥ w) i ∈ intL L := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem (fun j _ => mul_mem (hM i j) (hw j))

theorem iff_of_inverse {D E Q R Dg : Matrix (Fin N) (Fin N) L} (hED : E * D = 1) (hQ : IsInt (Q * E))
    (hR : IsInt (R * E)) (hDg : IsInt Dg) (hD : IsInt D) (e : D = Dg * R + D * Q) (B : Fin N → L) :
    (∀ i, (D *ᵥ B) i ∈ intL L) ↔ (∀ i, (Q *ᵥ B) i ∈ intL L) ∧ ∀ i, (R *ᵥ B) i ∈ intL L := by
  constructor
  · intro h
    have key : ∀ P : Matrix (Fin N) (Fin N) L, IsInt (P * E) → ∀ i, (P *ᵥ B) i ∈ intL L := by
      intro P hP i
      have hPB : P *ᵥ B = (P * E) *ᵥ (D *ᵥ B) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hED, Matrix.mul_one]
      rw [hPB]
      exact int_mulVec hP h i
    exact ⟨key Q hQ, key R hR⟩
  · rintro ⟨hq, hr⟩ i
    have hDB : D *ᵥ B = Dg *ᵥ (R *ᵥ B) + D *ᵥ (Q *ᵥ B) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← e]
    rw [hDB, Pi.add_apply]
    exact add_mem (int_mulVec hDg hr i) (int_mulVec hD hq i)

theorem dual : Dual := by
  unfold GlobalTheory.InertZeta.Dual
  intro L _ _ ϖ σ q N hU g U V C hF r b t hr
  obtain ⟨hσσ, hσv, -, -, -, -, -⟩ := hU
  obtain ⟨hUi, hVi, hCi, hAi, hUVC⟩ := hF
  have hg : cT σ (mat g) * antiJ L N * mat g = antiJ L N := g.2
  have hJJ : antiJ L N * antiJ L N = 1 := antiJ_mul_self
  have hJi : IsInt (antiJ L N) := isInt_antiJ
  have hmem : ∀ x : L, x ∈ intL L ↔ Valued.v x ≤ 1 := fun x => Valuation.mem_integer_iff _ _
  have hsub : ∀ {X Y : Matrix (Fin N) (Fin N) L}, IsInt X → IsInt Y → IsInt (X - Y) :=
    fun hX hY i j => sub_mem (hX i j) (hY i j)
  have hcTmul : ∀ X Y : Matrix (Fin N) (Fin N) L, cT σ (X * Y) = cT σ Y * cT σ X := by
    intro X Y
    simp [cT, Matrix.map_mul, Matrix.transpose_mul]
  have hcTone : cT σ (1 : Matrix (Fin N) (Fin N) L) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [cT]
    · simp [cT, Matrix.one_apply, h, Ne.symm h]
  have hGJ : mat g * antiJ L N * cT σ (mat g) = antiJ L N := by
    have h1 : (antiJ L N * cT σ (mat g) * antiJ L N) * mat g = 1 := by
      rw [show antiJ L N * cT σ (mat g) * antiJ L N * mat g
          = antiJ L N * (cT σ (mat g) * antiJ L N * mat g) by simp only [Matrix.mul_assoc], hg, hJJ]
    have h2 := mul_eq_one_comm.mp h1
    calc mat g * antiJ L N * cT σ (mat g)
        = mat g * (antiJ L N * cT σ (mat g) * antiJ L N) * antiJ L N := by
          simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = antiJ L N := by rw [h2, Matrix.one_mul]
  have hCUV : C * (U + V * mat g) = 1 := mul_eq_one_comm.mp hUVC
  have hCUV' : C * U + C * V * mat g = 1 := by
    rw [Matrix.mul_assoc C V, ← Matrix.mul_add]
    exact hCUV
  have hED : (antiJ L N * cT σ (U + V * mat g)) * (cT σ C * antiJ L N) = 1 := by
    calc (antiJ L N * cT σ (U + V * mat g)) * (cT σ C * antiJ L N)
        = antiJ L N * cT σ (C * (U + V * mat g)) * antiJ L N := by
          rw [hcTmul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCUV, hcTone, Matrix.mul_one, hJJ]
  have hD : IsInt (cT σ C * antiJ L N) := (isInt_cT hσv hCi).mul hJi
  have hDg : IsInt (cT σ (mat g * C) * antiJ L N) := (isInt_cT hσv hAi).mul hJi
  have he : cT σ C * antiJ L N
      = cT σ (mat g * C) * antiJ L N * (mat g * C * U) + cT σ C * antiJ L N * (C * V * mat g) := by
    have h1 : cT σ C * cT σ (mat g) * antiJ L N * (mat g * C * U) = cT σ C * antiJ L N * (C * U) := by
      calc cT σ C * cT σ (mat g) * antiJ L N * (mat g * C * U)
          = cT σ C * (cT σ (mat g) * antiJ L N * mat g) * (C * U) := by simp only [Matrix.mul_assoc]
        _ = cT σ C * antiJ L N * (C * U) := by rw [hg]
    rw [hcTmul, h1, ← Matrix.mul_add, hCUV', Matrix.mul_one]
  have hcTU : IsInt (cT σ U) := isInt_cT hσv hUi
  have hcTV : IsInt (cT σ V) := isInt_cT hσv hVi
  have hQE : IsInt (C * V * mat g * (antiJ L N * cT σ (U + V * mat g))) := by
    have hCVG : C * V * mat g = 1 - C * U := eq_sub_of_add_eq' hCUV'
    have h2 : C * V * mat g * (antiJ L N * (cT σ (mat g) * cT σ V)) = C * V * (antiJ L N * cT σ V) := by
      calc C * V * mat g * (antiJ L N * (cT σ (mat g) * cT σ V))
          = C * V * (mat g * antiJ L N * cT σ (mat g)) * cT σ V := by simp only [Matrix.mul_assoc]
        _ = C * V * (antiJ L N * cT σ V) := by rw [hGJ]; simp only [Matrix.mul_assoc]
    rw [cT_add, hcTmul, Matrix.mul_add (antiJ L N), Matrix.mul_add, h2, hCVG, Matrix.sub_mul, Matrix.one_mul]
    exact (hsub (hJi.mul hcTU) ((hCi.mul hUi).mul (hJi.mul hcTU))).add ((hCi.mul hVi).mul (hJi.mul hcTV))
  have hRE : IsInt (mat g * C * U * (antiJ L N * cT σ (U + V * mat g))) := by
    have hCU : C * U = 1 - C * V * mat g := eq_sub_of_add_eq hCUV'
    have hA : mat g * (antiJ L N * cT σ (mat g)) * cT σ V = antiJ L N * cT σ V := by
      rw [← Matrix.mul_assoc (mat g) (antiJ L N), hGJ]
    have hB : mat g * (C * V * mat g) * (antiJ L N * cT σ (mat g)) * cT σ V
        = mat g * C * V * (antiJ L N * cT σ V) := by
      calc mat g * (C * V * mat g) * (antiJ L N * cT σ (mat g)) * cT σ V
          = mat g * C * V * (mat g * antiJ L N * cT σ (mat g)) * cT σ V := by simp only [Matrix.mul_assoc]
        _ = mat g * C * V * (antiJ L N * cT σ V) := by rw [hGJ]; simp only [Matrix.mul_assoc]
    have h3 : mat g * C * U * (antiJ L N * (cT σ (mat g) * cT σ V))
        = antiJ L N * cT σ V - mat g * C * V * (antiJ L N * cT σ V) := by
      calc mat g * C * U * (antiJ L N * (cT σ (mat g) * cT σ V))
          = mat g * (C * U) * (antiJ L N * cT σ (mat g)) * cT σ V := by simp only [Matrix.mul_assoc]
        _ = mat g * (1 - C * V * mat g) * (antiJ L N * cT σ (mat g)) * cT σ V := by rw [hCU]
        _ = antiJ L N * cT σ V - mat g * C * V * (antiJ L N * cT σ V) := by
          rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.sub_mul, hA, hB]
    rw [cT_add, hcTmul, Matrix.mul_add (antiJ L N), Matrix.mul_add, h3]
    exact ((hAi.mul hUi).mul (hJi.mul hcTU)).add (hsub (hJi.mul hcTV) ((hAi.mul hVi).mul (hJi.mul hcTV)))
  have hJb : antiJ L N *ᵥ b = fun k => b k.rev := funext (antiJ_mulVec b)
  have hσvec : ∀ j, σ (vecMul r C j) = -((cT σ C * antiJ L N) *ᵥ b) j := by
    intro j
    rw [← Matrix.mulVec_mulVec, hJb]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, Matrix.transpose_apply, Matrix.map_apply,
      map_sum, map_mul, hr, map_neg, hσσ, neg_mul, Finset.sum_neg_distrib, neg_inj]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hL : ∀ j, (t * vecMul r C j ∈ intL L ↔ t * ((cT σ C * antiJ L N) *ᵥ b) j ∈ intL L) := by
    intro j
    rw [hmem, hmem, Valuation.map_mul, Valuation.map_mul, ← hσv (vecMul r C j), hσvec j, Valuation.map_neg]
  have key := iff_of_inverse (D := cT σ C * antiJ L N) (E := antiJ L N * cT σ (U + V * mat g))
    (Q := C * V * mat g) (R := mat g * C * U) (Dg := cT σ (mat g * C) * antiJ L N)
    hED hQE hRE hDg hD he (t • b)
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at key
  rw [forall_congr' hL]
  exact key

end GlobalTheory.CompanionTheory.InertDual

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.FractionExistsOfSmith
section
open Matrix

namespace GlobalTheory.CompanionTheory.InertZeta

open GlobalTheory.InertZeta

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem isInt_diagonal {f : Fin n → L} (hf : ∀ i, f i ∈ Formalism.UG.intL L) : IsInt (Matrix.diagonal f) := fun i j => by
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · exact hf i
  · exact zero_mem _

theorem hasLen_diagonal {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (d : Fin n → ℤ) :
    HasLen (Matrix.diagonal fun i => ϖ ^ d i) (∑ i, (-d i).toNat) := by
  have h0 : ϖ ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have h1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hpow : ∀ e : ℕ, ϖ ^ e ∈ Formalism.UG.intL L := fun e => by
    change Valued.v (ϖ ^ e) ≤ 1
    rw [map_pow]
    exact pow_le_one' h1 e
  have hnum : ∀ i, ϖ ^ d i * ϖ ^ (-d i).toNat = ϖ ^ (d i).toNat := fun i => by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0]
    congr 1
    omega
  refine ⟨Matrix.diagonal fun i => if 0 ≤ d i then 1 else 0, Matrix.diagonal fun i => if 0 ≤ d i then 0 else 1,
    Matrix.diagonal fun i => ϖ ^ (-d i).toNat, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · refine isInt_diagonal fun i => ?_
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · refine isInt_diagonal fun i => ?_
    split_ifs
    · exact zero_mem _
    · exact one_mem _
  · exact isInt_diagonal fun i => hpow _
  · rw [Matrix.diagonal_mul_diagonal]
    refine isInt_diagonal fun i => ?_
    rw [hnum]
    exact hpow _
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    by_cases h : 0 ≤ d i
    · have : (-d i).toNat = 0 := by omega
      simp [h, this]
    · have e : ϖ ^ d i * ϖ ^ (-d i).toNat = 1 := by
        rw [hnum, show (d i).toNat = 0 by omega, pow_zero]
      simp [h, e]
  · rw [Matrix.det_diagonal, map_prod]
    simp only [map_pow, hϖ]
    rw [Finset.prod_pow_eq_pow_sum, ← WithZero.exp_nsmul]
    congr 1
    simp

theorem fracExists_of_smith : Smith → FracExists := by
  intro hS L _ _ ϖ n hϖ g hg
  obtain ⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, rfl⟩ := hS L ϖ n hϖ g hg
  have h := (hasLen_diagonal hϖ d).mul_mul ha ha' hb hb' ea eb
  rw [h.len_eq]
  exact h

end GlobalTheory.CompanionTheory.InertZeta
end

