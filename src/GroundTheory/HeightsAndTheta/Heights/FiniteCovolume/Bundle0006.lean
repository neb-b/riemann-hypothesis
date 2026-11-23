module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDiscreteFundamentalDomain
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory Set Topology

theorem DiscreteFundamentalDomain.proof (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] : DiscreteFundamentalDomain.Statement G := by
  classical
  intro μ Γ hΓ

  have hcount : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance

  obtain ⟨t, ht, hteq⟩ := isOpen_induced_iff.mp (isOpen_discrete ({1} : Set Γ))
  have h1t : (1 : G) ∈ t := by
    have : (1 : Γ) ∈ ((↑) : Γ → G) ⁻¹' t := by rw [hteq]; rfl
    simpa using this

  obtain ⟨V, hVo, hV1, hVV⟩ := exists_open_nhds_one_split (ht.mem_nhds h1t)
  let U : Set G := V ∩ Inv.inv ⁻¹' V
  have hUo : IsOpen U := hVo.inter (hVo.preimage continuous_inv)
  have hU1 : (1 : G) ∈ U := ⟨hV1, by simpa using hV1⟩
  have key : ∀ u ∈ U, ∀ w ∈ U, ∀ γ : Γ, (γ : G) = u * w⁻¹ → γ = 1 := by
    intro u hu w hw γ hγ
    have h : (γ : G) ∈ t := hγ ▸ hVV u hu.1 w⁻¹ hw.2
    have h' : γ ∈ ((↑) : Γ → G) ⁻¹' t := h
    rw [hteq] at h'
    exact h'

  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun g : G => (fun x => x * g⁻¹) ⁻¹' U) (fun g => hUo.preimage (continuous_mul_const _))
  have hall : ∀ x : G, x ∈ ⋃ g : G, (fun x => x * g⁻¹) ⁻¹' U := fun x =>
    mem_iUnion.2 ⟨x, by simpa using hU1⟩
  have hTne : T.Nonempty := by
    have h := hall 1
    rw [← hTU] at h
    obtain ⟨g, hg, -⟩ := mem_iUnion₂.1 h
    exact ⟨g, hg⟩
  obtain ⟨g, hg⟩ := hTc.exists_eq_range hTne
  let A : ℕ → Set G := fun n => (fun x => x * (g n)⁻¹) ⁻¹' U
  have hAo : ∀ n, IsOpen (A n) := fun n => hUo.preimage (continuous_mul_const _)
  have hcover : ∀ x : G, ∃ n, x ∈ A n := by
    intro x
    have h := hall x
    rw [← hTU, hg] at h
    obtain ⟨_, ⟨n, rfl⟩, hx⟩ := mem_iUnion₂.1 h
    exact ⟨n, hx⟩

  let FD : Set G :=
    ⋃ n, A n ∩ ⋂ m, ⋂ (_ : m < n), ⋂ γ : Γ, (fun x => (γ : G) * x) ⁻¹' (A m)ᶜ
  have memFD : ∀ y, y ∈ FD ↔ ∃ n, y ∈ A n ∧ ∀ m < n, ∀ γ : Γ, (γ : G) * y ∉ A m := by
    intro y
    simp only [FD, mem_iUnion, mem_inter_iff, mem_iInter, mem_preimage, mem_compl_iff]
  have hmeas : MeasurableSet FD :=
    MeasurableSet.iUnion fun n => (hAo n).measurableSet.inter <|
      MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun γ =>
        (hAo m).measurableSet.compl.preimage (continuous_const_mul _).measurable

  have uniq : ∀ y, ∀ δ : Γ, y ∈ FD → (δ : G) * y ∈ FD → δ = 1 := by
    intro y δ hy hδy
    obtain ⟨n₁, hy₁, hy₂⟩ := (memFD y).1 hy
    obtain ⟨n₂, hδ₁, hδ₂⟩ := (memFD _).1 hδy
    rcases lt_trichotomy n₁ n₂ with h | rfl | h
    · exact absurd (by simpa using hy₁) (hδ₂ n₁ h δ⁻¹)
    · refine key _ hδ₁ _ hy₁ δ ?_
      group
    · exact absurd hδ₁ (hy₂ n₂ h δ)
  refine ⟨FD, hmeas, IsFundamentalDomain.mk' hmeas.nullMeasurableSet fun x => ?_⟩

  have hP : ∃ n, ∃ γ : Γ, (γ : G) * x ∈ A n := by
    obtain ⟨n, hn⟩ := hcover x
    exact ⟨n, 1, by simpa using hn⟩
  obtain ⟨γ, hγ⟩ := Nat.find_spec hP
  have hγFD : (γ : G) * x ∈ FD := by
    refine (memFD _).2 ⟨Nat.find hP, hγ, fun m hm δ hδ => Nat.find_min hP hm ⟨δ * γ, ?_⟩⟩
    simpa [mul_assoc] using hδ
  refine ⟨γ, by simpa [Subgroup.smul_def] using hγFD, fun δ hδ => ?_⟩
  have hδ' : (δ : G) * x ∈ FD := by simpa [Subgroup.smul_def] using hδ
  have h1 := uniq _ (δ * γ⁻¹) hγFD (by simpa [mul_assoc] using hδ')
  simpa [mul_inv_eq_one] using h1

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PEigenReflection
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix
open scoped ComplexOrder

private lemma expand_sandwich {ι : Type*} [Fintype ι] [DecidableEq ι] (M X X' Y : Matrix ι ι ℂ) (c a b d : ℂ)
    (h1 : X' * M = a • Y) (h2 : M * X = b • Y) (h3 : X' * M * X = d • Y) :
    (1 - c • X') * M * (1 - c • X) = M + (c * c * d - c * a - c * b) • Y := by
  have e : (1 - c • X') * M * (1 - c • X) =
      M - c • (X' * M) - c • (M * X) + (c * c) • (X' * M * X) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_sub,
      smul_smul]
    abel
  rw [e, h3, h1, h2]
  simp only [smul_smul, sub_smul]
  abel

theorem EigenReflection.proof (ι : Type*) [Fintype ι] [DecidableEq ι] :
    EigenReflection.Statement ι := by
  intro H P hmaj ε hε v hv hAv
  obtain ⟨hP, hH, -, hPHP⟩ := hmaj
  have hPh : Pᴴ = P := hP.isHermitian
  have hHh : Hᴴ = H := hH
  set y : ι → ℂ := P *ᵥ v with hy
  set q : ℂ := star v ⬝ᵥ (P *ᵥ v) with hqdef
  have hqpos : 0 < q := hP.dotProduct_mulVec_pos hv
  have hq0 : q ≠ 0 := hqpos.ne'
  have hqstar : star q = q := Complex.conj_eq_iff_im.mpr (Complex.pos_iff.mp hqpos).2.symm
  have hεstar : star ε = ε := by rcases hε with rfl | rfl <;> simp
  set c : ℂ := 2 / q with hc
  have hcstar : star c = c := by rw [hc, star_div₀, hqstar]; simp
  have hcq : c * q = 2 := by rw [hc]; field_simp

  have hwy : star v ᵥ* P = star y := by rw [hy, star_mulVec, hPh]
  have hyv : star y ⬝ᵥ v = q := by rw [← hwy, ← dotProduct_mulVec]

  have hHv : H *ᵥ v = ε • y := by
    have : H *ᵥ v = P *ᵥ ((H⁻¹ * P) *ᵥ v) := by rw [mulVec_mulVec, ← Matrix.mul_assoc, hPHP]
    rw [this, show (H⁻¹ * P) *ᵥ v = ε • v from hAv, mulVec_smul]
  have hvH : star v ᵥ* H = ε • star y := by
    rw [← hHh, ← star_mulVec, hHv, star_smul, hεstar]

  have hR : pReflection P v = 1 - c • vecMulVec v (star y) := by
    rw [pReflection, ← hqdef, ← hc, vecMulVec_mul, hwy]
  have hRh : (pReflection P v)ᴴ = 1 - c • vecMulVec y (star v) := by
    rw [hR, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hcstar,
      conjTranspose_vecMulVec, star_star]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hRh, hR]
    have h1 : vecMulVec y (star v) * P = (1 : ℂ) • vecMulVec y (star y) := by
      rw [vecMulVec_mul, hwy, one_smul]
    have h2 : P * vecMulVec v (star y) = (1 : ℂ) • vecMulVec y (star y) := by
      rw [mul_vecMulVec, ← hy, one_smul]
    have h3 : vecMulVec y (star v) * P * vecMulVec v (star y) = q • vecMulVec y (star y) := by
      rw [vecMulVec_mul, hwy, vecMulVec_mul_vecMulVec, hyv, vecMulVec_smul]
    rw [expand_sandwich P _ _ _ c 1 1 q h1 h2 h3]
    have : c * c * q - c * 1 - c * 1 = 0 := by
      rw [mul_assoc, hcq]; ring
    rw [this, zero_smul, add_zero]
  · rw [hRh, hR]
    have h1 : vecMulVec y (star v) * H = ε • vecMulVec y (star y) := by
      rw [vecMulVec_mul, hvH, vecMulVec_smul]
    have h2 : H * vecMulVec v (star y) = ε • vecMulVec y (star y) := by
      rw [mul_vecMulVec, hHv]
      ext i j
      simp [vecMulVec_apply, mul_assoc]
    have h3 : vecMulVec y (star v) * H * vecMulVec v (star y) = (ε * q) • vecMulVec y (star y) := by
      rw [vecMulVec_mul, hvH, vecMulVec_mul_vecMulVec, smul_dotProduct, hyv, vecMulVec_smul]
      rfl
    rw [expand_sandwich H _ _ _ c ε ε (ε * q) h1 h2 h3]
    have : c * c * (ε * q) - c * ε - c * ε = 0 := by
      have : c * c * (ε * q) = (c * q) * c * ε := by ring
      rw [this, hcq]; ring
    rw [this, zero_smul, add_zero]
  · rw [hR, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hyv]
    rw [op_smul_eq_smul, smul_smul, hcq, two_smul]; abel
  · intro u hu
    have hyu : star y ⬝ᵥ u = 0 := by rw [← hwy, ← dotProduct_mulVec, hu]
    rw [hR, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hyu]
    simp

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PEigenReflectionMaps
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix
open scoped ComplexOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem star_dotProduct_mulVec_of_isHermitian {P : Matrix ι ι ℂ} (hP : P.IsHermitian)
    (x y : ι → ℂ) : star (star y ⬝ᵥ (P *ᵥ x)) = star x ⬝ᵥ (P *ᵥ y) := by
  have h1 : star y ⬝ᵥ (P *ᵥ x) = star (P *ᵥ y) ⬝ᵥ x := by
    rw [dotProduct_mulVec, star_mulVec, hP.eq]
  rw [h1, star_dotProduct, star_star]

theorem exists_unit_mul_star_eq_norm (s : ℂ) : ∃ α : ℂ, ‖α‖ = 1 ∧ α * star s = ‖s‖ ∧ star α * s = ‖s‖ := by
  by_cases hs : s = 0
  · exact ⟨1, by simp, by simp [hs], by simp [hs]⟩
  · have hn : (‖s‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hs
    refine ⟨s / ‖s‖, ?_, ?_, ?_⟩
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.mpr hs)]
    · rw [div_mul_eq_mul_div, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      field_simp
      push_cast; ring
    · rw [star_div₀, Complex.star_def, Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
      field_simp
      push_cast; ring


variable (ι) in
theorem EigenReflectionMaps.proof (h₁ : EigenReflection.Statement ι)
    (h₂ : EigenspacesOrthogonal.Statement ι) : EigenReflectionMaps.Statement ι := by
  intro H P hMaj ε hε a a' ha ha' hρ
  have hPh : P.IsHermitian := hMaj.1.isHermitian
  obtain ⟨α, hα1, hαs, hαs'⟩ := exists_unit_mul_star_eq_norm (star a ⬝ᵥ (P *ᵥ a'))
  refine ⟨α, hα1, ?_⟩
  set v : ι → ℂ := a' - α • a with hv
  by_cases hv0 : v = 0
  · refine ⟨1, by simp, by simp, ?_, fun u _ => by simp⟩
    rw [one_mulVec]
    exact sub_eq_zero.mp hv0
  have hAv : majInvolution H P *ᵥ v = ε • v := by
    rw [hv, mulVec_sub, mulVec_smul, ha, ha', smul_sub, smul_comm]
  obtain ⟨hRP, hRH, hRv, hRfix⟩ := h₁ H P hMaj ε hε v hv0 hAv
  refine ⟨pReflection P v, hRP, hRH, ?_, ?_⟩
  ·
    have hconj : star a' ⬝ᵥ (P *ᵥ a) = star (star a ⬝ᵥ (P *ᵥ a')) :=
      (star_dotProduct_mulVec_of_isHermitian hPh a' a).symm
    have hαα : star α * α = 1 := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hα1]; simp
    have hw : star v ⬝ᵥ (P *ᵥ (a' + α • a)) = 0 := by
      rw [hv, star_sub, star_smul, mulVec_add, mulVec_smul, sub_dotProduct, dotProduct_add,
        dotProduct_add, smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul,
        hconj, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, ← hρ]
      have e1 : star α * (α * (star a ⬝ᵥ (P *ᵥ a))) = (star α * α) * (star a ⬝ᵥ (P *ᵥ a)) := by
        ring
      rw [e1, hαα, hαs, hαs']
      ring
    have hRw := hRfix _ hw
    have hsplit : a' = (1 / 2 : ℂ) • (a' + α • a) + (1 / 2 : ℂ) • v := by
      rw [hv]; ext i; simp; ring
    rw [hsplit, mulVec_add, mulVec_smul, mulVec_smul, hRw, hRv, hv]
    ext i; simp; ring
  · intro u hu
    apply hRfix
    rcases hε with rfl | rfl
    · have h := h₂ H P hMaj v u (by rw [hAv, one_smul]) (by rw [hu, neg_smul, one_smul])
      exact h
    · have h := h₂ H P hMaj u v (by rw [hu, neg_neg, one_smul]) (by rw [hAv, neg_smul, one_smul])
      rw [← star_dotProduct_mulVec_of_isHermitian hPh, h, star_zero]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHermAtPlace
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

section Places

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem HermAtPlace.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    HermAtPlace.Statement h v := by
  intro w x y
  rw [sesq_eq_sum h.toSesq v x y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, embedding_conj, dotProduct, mulVec, gramAt, vecAt, Pi.star_apply,
    Matrix.map_apply, Finset.mul_sum, RCLike.star_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Places

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIdealClassesFinite
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

section Numbers

variable {E : Type*} [Field E] [NumberField E]

def scaledIdeal (I : AddSubgroup E) (hI : ∀ a : 𝓞 E, ∀ x ∈ I, (a : E) * x ∈ I) (b : E) :
    Ideal (𝓞 E) where
  carrier := {y | b⁻¹ * (y : E) ∈ I}
  add_mem' := by
    intro y z hy hz
    simp only [Set.mem_ofPred_eq] at *
    have h := I.add_mem hy hz
    convert h using 1
    push_cast
    ring
  zero_mem' := by simp [I.zero_mem]
  smul_mem' := by
    intro a y hy
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at *
    have h := hI a _ hy
    convert h using 1
    push_cast
    ring

theorem mem_scaledIdeal {I : AddSubgroup E} {hI : ∀ a : 𝓞 E, ∀ x ∈ I, (a : E) * x ∈ I} {b : E}
    {y : 𝓞 E} : y ∈ scaledIdeal I hI b ↔ b⁻¹ * (y : E) ∈ I := Iff.rfl

end Numbers

theorem IdealClassesFinite.proof (E) [Field E] [NumberField E] : IdealClassesFinite.Statement E := by
  classical
  let rep : ClassGroup (𝓞 E) → nonZeroDivisors (Ideal (𝓞 E)) := fun c => (ClassGroup.mk0_surjective c).choose
  have hrep : ∀ c, ClassGroup.mk0 (rep c) = c := fun c => (ClassGroup.mk0_surjective c).choose_spec
  let J : ClassGroup (𝓞 E) → AddSubgroup E := fun c =>
    ((rep c : Ideal (𝓞 E)).toAddSubgroup).map (algebraMap (𝓞 E) E).toAddMonoidHom
  refine ⟨Set.range J, Set.finite_range J, ?_⟩
  intro I hfg hne hI
  obtain ⟨S, hS⟩ := hfg
  obtain ⟨⟨b, hb0⟩, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) (S : Finset E)
  have hbne : (b : E) ≠ 0 := by
    have : b ≠ 0 := nonZeroDivisors.ne_zero hb0
    exact_mod_cast this
  have hint : ∀ x ∈ I, ∃ w : 𝓞 E, (w : E) = b * x := by
    have hall : ∀ t : I, ∃ w : 𝓞 E, (w : E) = b * (t : E) := by
      intro t
      have ht : t ∈ AddSubsemigroup.closure (S : Set I) := by rw [hS]; trivial
      induction ht using AddSubsemigroup.closure_induction with
      | mem t ht =>
        obtain ⟨w, hw⟩ := hb t (by simpa using Finset.mem_image_of_mem Subtype.val ht)
        exact ⟨w, by rw [Algebra.smul_def] at hw; exact hw⟩
      | add x y _ _ hx hy =>
        obtain ⟨w, hw⟩ := hx
        obtain ⟨v, hv⟩ := hy
        exact ⟨w + v, by push_cast; linear_combination hw + hv⟩
    intro x hx
    exact hall ⟨x, hx⟩
  let 𝔞 := scaledIdeal I hI (b : E)
  have hmem : ∀ z ∈ I, ∀ w : 𝓞 E, (w : E) = b * z → w ∈ 𝔞 := by
    intro z hz w hw
    rw [mem_scaledIdeal, hw, ← mul_assoc, inv_mul_cancel₀ hbne, one_mul]
    exact hz
  have h𝔞 : 𝔞 ∈ nonZeroDivisors (Ideal (𝓞 E)) := by
    apply mem_nonZeroDivisors_of_ne_zero
    obtain ⟨z, hz, hz0⟩ := (AddSubgroup.bot_or_exists_ne_zero I).resolve_left hne
    obtain ⟨w, hw⟩ := hint z hz
    intro h0
    have hw𝔞 : w ∈ 𝔞 := hmem z hz w hw
    rw [h0, Submodule.zero_eq_bot, Ideal.mem_bot] at hw𝔞
    rw [hw𝔞] at hw
    push_cast at hw
    exact hz0 ((mul_eq_zero.1 hw.symm).resolve_left hbne)
  set c := ClassGroup.mk0 ⟨𝔞, h𝔞⟩
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 (hrep c).symm
  have hxE : (x : E) ≠ 0 := by exact_mod_cast hx
  have hyE : (y : E) ≠ 0 := by exact_mod_cast hy
  refine ⟨J c, ⟨c, rfl⟩, (y : E) / ((x : E) * b), div_ne_zero hyE (mul_ne_zero hxE hbne), ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := hint z hz
    have hxw : x * w ∈ Ideal.span {y} * (rep c : Ideal (𝓞 E)) :=
      hxy ▸ Ideal.mem_span_singleton_mul.2 ⟨w, hmem z hz w hw, rfl⟩
    obtain ⟨v, hv, hvw⟩ := Ideal.mem_span_singleton_mul.1 hxw
    have hvw' : (y : E) * v = x * (b * z) := by
      rw [← hw]; exact_mod_cast hvw
    refine AddSubgroup.mem_map.2 ⟨(v : E), AddSubgroup.mem_map.2 ⟨v, hv, rfl⟩, ?_⟩
    simp only [AddMonoidHom.coe_mulLeft]
    field_simp
    linear_combination hvw'
  · intro hz
    obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.1 hz
    obtain ⟨v, hv, rfl⟩ := AddSubgroup.mem_map.1 hu
    have hyv : y * v ∈ Ideal.span {x} * 𝔞 :=
      hxy.symm ▸ Ideal.mem_span_singleton_mul.2 ⟨v, hv, rfl⟩
    obtain ⟨w, hw, hwv⟩ := Ideal.mem_span_singleton_mul.1 hyv
    have hwv' : (x : E) * w = y * v := by exact_mod_cast hwv
    rw [mem_scaledIdeal] at hw
    convert hw using 1
    simp only [AddMonoidHom.coe_mulLeft, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    field_simp
    linear_combination -hwv'

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIndexLeDet
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module Matrix

theorem IndexLeDet.proof (E : Type*) [Field E] [NumberField E] : IndexLeDet.Statement E := by
  classical
  intro A hA e a T ha hT
  have hmem : ∀ i, (a i : E) ∈ A := fun i => hA ⟨a i, rfl⟩
  let b : Fin (finrank ℚ E) → A := fun i => ⟨a i, hmem i⟩
  have hb : ∀ i, b i = ∑ j, T i j • e j := by
    intro i
    apply Subtype.ext
    simp [b, hT i]

  have hdet : T.det ≠ 0 := by
    intro h0
    have h0' : ((Int.castRingHom ℚ).mapMatrix T).det = 0 := by
      rw [← RingHom.map_det, h0, map_zero]
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0'
    have hsum : ∑ i, v i • (a i : E) = 0 := by
      calc ∑ i, v i • (a i : E)
          = ∑ i, ∑ j, (v i * (T i j : ℚ)) • (e j : E) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hT i, Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
        _ = ∑ j, (∑ i, v i * (T i j : ℚ)) • (e j : E) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_smul]
        _ = 0 := by
            refine Finset.sum_eq_zero fun j _ => ?_
            have := congrFun hv j
            simp only [vecMul, dotProduct, RingHom.mapMatrix_apply, map_apply, eq_intCast,
              Pi.zero_apply] at this
            rw [this, zero_smul]
    exact hv0 (funext fun i => Fintype.linearIndependent_iff.mp ha v hsum i)

  have hliE : LinearIndependent ℤ (fun i => (a i : E)) := ha.restrict_scalars' ℤ
  have hli : LinearIndependent ℤ b :=
    LinearIndependent.of_comp (A.subtype.toIntLinearMap) hliE
  have : Module.Free ℤ A := Module.Free.of_basis e
  have : Module.Finite ℤ A := Module.Finite.of_basis e
  set N := Submodule.span ℤ (Set.range b) with hN
  let bN := Basis.span hli
  have hbN : ((↑) ∘ bN : Fin (finrank ℚ E) → A) = b := funext fun i => congrArg Subtype.val (Basis.span_apply hli i)
  have hcard := Submodule.natAbs_det_basis_change e N bN
  rw [hbN] at hcard
  have hdetb : e.det b = T.det := by
    rw [Basis.det_apply, ← Matrix.det_transpose]
    congr 1
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.transpose_apply, Basis.toMatrix_apply, hb i, map_sum]
    simp [Finsupp.single_apply]
  rw [hdetb] at hcard

  have hle : N.toAddSubgroup ≤ (intSubgroup E).addSubgroupOf A := by
    have : N ≤ ((intSubgroup E).addSubgroupOf A).toIntSubmodule := by
      rw [hN, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show b i ∈ (intSubgroup E).addSubgroupOf A
      rw [AddSubgroup.mem_addSubgroupOf]
      exact ⟨a i, rfl⟩
    exact this
  have hidx : N.toAddSubgroup.index = T.det.natAbs := hcard.symm
  have hdvd := AddSubgroup.index_dvd_of_le hle
  rw [hidx] at hdvd
  have hle' : (intSubgroup E).relIndex A ≤ T.det.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hdet) hdvd
  calc ((intSubgroup E).relIndex A : ℝ) ≤ (T.det.natAbs : ℝ) := by exact_mod_cast hle'
    _ = |(T.det : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

