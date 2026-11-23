module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdaptedExponentSchwartzBruhatLastColumn
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.AdaptedExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eventually_pow_le {ϖ : kˣ} (h : IsUnif ϖ) (s : kˣ) :
    ∀ᶠ e : ℕ in Filter.atTop, valuation k ((ϖ ^ e : kˣ) : k) ≤ valuation k (s : k) := by
  have h1 : valuation k (ϖ : k) < 1 := (h _).2 le_rfl
  have hs : valuation k (s : k) ≠ 0 := by simp
  obtain ⟨m, hm⟩ := exists_pow_lt₀ h1 (Units.mk0 _ hs)
  filter_upwards [Filter.eventually_ge_atTop m] with e he
  rw [Units.val_pow_eq_pow_val, map_pow]
  exact (pow_le_pow_right_of_le_one' h1.le he).trans hm.le

theorem eventually_subset_cball {ϖ : kˣ} (h : IsUnif ϖ) {K : Set k} (hK : IsCompact K) :
    ∀ᶠ e : ℕ in Filter.atTop, K ⊆ cball (ϖ ^ e)⁻¹ := by
  have key : ∀ s : kˣ, ∀ᶠ e : ℕ in Filter.atTop, cball s ⊆ cball (ϖ ^ e)⁻¹ := by
    intro s
    filter_upwards [eventually_pow_le h s⁻¹] with e he x hx
    have hs : 0 < valuation k (s : k) := by simp [pos_iff_ne_zero]
    have he0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := by
      rw [pos_iff_ne_zero]; simp
    simp only [cball, Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at hx he ⊢
    exact hx.trans ((le_inv_comm₀ he0 hs).1 he)
  refine hK.induction_on (p := fun K => ∀ᶠ e : ℕ in Filter.atTop, K ⊆ cball (ϖ ^ e)⁻¹)
    (by simp) ?_ ?_ ?_
  · intro s t hst ht
    exact ht.mono fun e he => hst.trans he
  · intro s t hs ht
    filter_upwards [hs, ht] with e h1 h2 using Set.union_subset h1 h2
  · intro x _
    by_cases hx : x = 0
    · subst hx
      exact ⟨cball 1, mem_nhdsWithin_of_mem_nhds (cball_mem_nhds 1), key 1⟩
    · exact ⟨cball (Units.mk0 x hx), mem_nhdsWithin_of_mem_nhds
        ((isOpen_cball _).mem_nhds (by simp [cball])), key _⟩

variable {n n' : Type}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem withCol_add (x₀ : Matrix n n' k) (y z : n → k) :
    withCol x₀ (y + z) = withCol x₀ y + withCol (0 : Matrix n n' k) z := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [withCol]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem continuous_withCol_zero :
    Continuous fun z : n → k => withCol (0 : Matrix n n' k) z := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases i with i | i <;> rcases j with j | j <;> simp only [withCol, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply] <;> fun_prop

theorem eventually_box_subset [Fintype n] {ϖ : kˣ} (h : IsUnif ϖ) {U : Set (n → k)}
    (hU : U ∈ 𝓝 (0 : n → k)) :
    ∀ᶠ e : ℕ in Filter.atTop, ∀ z ∈ box n (ϖ ^ e), z ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  choose s hs using fun i => exists_cball_subset (ht i)
  filter_upwards [Filter.eventually_all.2 fun i => eventually_pow_le h (s i)] with e he z hz
  exact hsub fun i _ => hs i (le_trans (hz i) (he i))

theorem eventually_adapted [Fintype n] [Fintype n'] {ϖ : kˣ} (h : IsUnif ϖ)
    {Ψ : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ}
    (hΨ : Ψ ∈ SB (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k)) :
    ∀ᶠ e : ℕ in Filter.atTop, ∀ (x₀ : Matrix n n' k) (y : n → k),
      (Ψ (withCol x₀ y) ≠ 0 → y ∈ box n (ϖ ^ e)⁻¹) ∧
        ∀ z ∈ box n (ϖ ^ e), Ψ (withCol x₀ (y + z)) = Ψ (withCol x₀ y) := by
  obtain ⟨Λ, hΛ, hinv⟩ := sb_matrix_exists_isOpen_addSubgroup k _ _ Ψ hΨ
  have hc : IsCompact (tsupport Ψ) := hΨ.2
  have h1 : ∀ r : n, ∀ᶠ e : ℕ in Filter.atTop,
      (fun x : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k => x (Sum.inl r) (Sum.inr 0)) ''
        tsupport Ψ ⊆ cball (ϖ ^ e)⁻¹ := fun r =>
    eventually_subset_cball h (hc.image (by fun_prop))
  have h0 : withCol (0 : Matrix n n' k) (0 : n → k) = 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [withCol]
  have h2 : (fun z : n → k => withCol (0 : Matrix n n' k) z) ⁻¹' (Λ : Set _) ∈ 𝓝 (0 : n → k) :=
    (hΛ.preimage continuous_withCol_zero).mem_nhds (by
      simp only [Set.mem_preimage, h0]; exact Λ.zero_mem)
  filter_upwards [Filter.eventually_all.2 h1, eventually_box_subset h h2] with e he1 he2 x₀ y
  refine ⟨fun hne r => ?_, fun z hz => ?_⟩
  · exact he1 r ⟨withCol x₀ y, subset_tsupport _ hne, rfl⟩
  · rw [withCol_add]
    exact hinv _ _ (he2 z hz)

theorem exists_adapted_exponent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (S : Set (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ)), S.Finite → (∀ Ψ ∈ S, Ψ ∈ SB (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k)) → ∀ ϖ : kˣ, IsUnif ϖ → ∃ e : ℕ, 1 ≤ e ∧ ∀ Ψ ∈ S, ∀ (x₀ : Matrix n n' k) (y : n → k), (Ψ (withCol x₀ y) ≠ 0 → y ∈ box n (ϖ ^ e)⁻¹) ∧ ∀ z ∈ box n (ϖ ^ e), Ψ (withCol x₀ (y + z)) = Ψ (withCol x₀ y) := by
  intro k _ _ _ _ n _ _ n' _ _ S hS hSB ϖ h
  exact ((Filter.eventually_ge_atTop 1).and ((Filter.eventually_all_finite hS).2
    fun Ψ hΨ => eventually_adapted h (hSB Ψ hΨ))).exists

end GlobalTheory.AdaptedExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEuclideanCoordsHermitianCartanInvolution
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace Real ComplexOrder

noncomputable section

namespace GlobalTheory.Twist.EuclidCoord

open GlobalTheory.RealWeil.UnitaryOsc


open scoped MatrixOrder in
theorem exists_coord : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H s : Matrix ι ι ℂ), Hᴴ = H → s * s = 1 → (H * s).PosDef → ∃ (E : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ)) (J : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι), (∀ x, J (J x) = -x) ∧ (∀ x, E (J x) = I • s *ᵥ E x) ∧ ∀ x y, (star (E y) ⬝ᵥ H *ᵥ E x).im = omJ J x y := by
  intro ι _ _ H s hH hs hpos
  have hP0 : (0 : Matrix ι ι ℂ) ≤ H * s := hpos.posSemidef.nonneg
  set R : Matrix ι ι ℂ := CFC.sqrt (H * s)
  have hR0 : (0 : Matrix ι ι ℂ) ≤ R := CFC.sqrt_nonneg _
  have hRh : Rᴴ = R := hR0.posSemidef.isHermitian.eq
  have hRR : R * R = H * s := CFC.sqrt_mul_sqrt_self _ hP0
  have hdet : R.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hRR
    rw [det_mul, h0, zero_mul] at e
    exact (hpos.det_pos.ne') (by rw [← e])
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det R).2 hdet.isUnit
  set s₀ : Matrix ι ι ℂ := u.1 * s * (u⁻¹).1 with hs₀
  have hs₀2 : s₀ * s₀ = 1 := by
    simp only [hs₀, mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc s, hs, one_mul, Units.mul_inv]

  have hRRs : u.1ᴴ * u.1 * s = H := by
    rw [hu, hRh, hRR, mul_assoc, hs, mul_one]
  have hform : (u⁻¹).1ᴴ * H * (u⁻¹).1 = s₀ := by
    rw [← hRRs]
    calc _ = (u.1 * (u⁻¹).1)ᴴ * (u.1 * s * (u⁻¹).1) := by simp only [mul_assoc, conjTranspose_mul]
      _ = s₀ := by simp [hs₀]
  have hs₀h : s₀ᴴ = s₀ := by
    rw [← hform, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH, mul_assoc]
  let E : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ) :=
    (crd ι).trans (ContinuousLinearEquiv.equivOfInverse (mvL (u⁻¹).1) (mvL u.1)
      (fun v => by
        change u.1 *ᵥ (u⁻¹).1 *ᵥ v = v
        rw [mulVec_mulVec, Units.mul_inv, one_mulVec])
      (fun v => by
        change (u⁻¹).1 *ᵥ u.1 *ᵥ v = v
        rw [mulVec_mulVec, Units.inv_mul, one_mulVec]))
  have hE : ∀ x, E x = (u⁻¹).1 *ᵥ crd ι x := fun _ => rfl
  refine ⟨E, cplx s₀ hs₀h hs₀2, cplx_cplx s₀ hs₀h hs₀2, fun x => ?_, fun x y => ?_⟩
  · rw [hE, hE, crd_cplx, mulVec_smul, mulVec_mulVec, mulVec_mulVec]
    congr 2
    rw [hs₀, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul]
  · rw [omJ_cplx, hE, hE, form_mulVec, hform]

end GlobalTheory.Twist.EuclidCoord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenericLevelOfFrame
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.GenericLevel

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_residueChar {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} (hϖ : IsUnif ϖ) :
    ∃ φ : AddChar 𝓀[k] Circle, ∀ x : 𝒪[k],
      φ (IsLocalRing.residue 𝒪[k] x) = ψ (((ϖ⁻¹ : kˣ) : k) * (x : k)) := by
  have hsurj : Function.Surjective (IsLocalRing.residue 𝒪[k]) := IsLocalRing.residue_surjective
  have h1 : ∀ y : k, valuation k y ≤ 1 → ψ y = 1 := by
    intro y hy
    exact (hψ 1).2 (by simp) y (by simpa using hy)
  have key : ∀ x y : 𝒪[k], IsLocalRing.residue 𝒪[k] x = IsLocalRing.residue 𝒪[k] y →
      ψ (((ϖ⁻¹ : kˣ) : k) * (x : k)) = ψ (((ϖ⁻¹ : kˣ) : k) * (y : k)) := by
    intro x y hxy
    have h2 := (hϖ _).1 ((residue_eq_iff_lt x y).1 hxy)
    have h0 : valuation k (ϖ : k) ≠ 0 := by simp
    have h3 : valuation k (((ϖ⁻¹ : kˣ) : k) * ((x : k) - (y : k))) ≤ 1 := by
      rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      exact (inv_mul_le_one₀ (zero_lt_iff.2 h0)).2 h2
    have h4 : ((ϖ⁻¹ : kˣ) : k) * (x : k)
        = ((ϖ⁻¹ : kˣ) : k) * (y : k) + ((ϖ⁻¹ : kˣ) : k) * ((x : k) - (y : k)) := by ring
    rw [h4, AddChar.map_add_eq_mul, h1 _ h3, mul_one]
  let f : 𝓀[k] → Circle := fun t => ψ (((ϖ⁻¹ : kˣ) : k) * ((Function.surjInv hsurj t : 𝒪[k]) : k))
  have hf : ∀ x : 𝒪[k], f (IsLocalRing.residue 𝒪[k] x) = ψ (((ϖ⁻¹ : kˣ) : k) * (x : k)) :=
    fun x => key _ _ (Function.surjInv_eq hsurj _)
  refine ⟨⟨f, ?_, ?_⟩, hf⟩
  · have := hf 0
    simpa using this
  · intro s t
    obtain ⟨x, rfl⟩ := hsurj s
    obtain ⟨y, rfl⟩ := hsurj t
    rw [← map_add (f := _), hf, hf, hf, ← AddChar.map_add_eq_mul]
    congr 1
    push_cast
    ring

end

section
variable {F a : Type} [Field F] [Fintype a] [DecidableEq a]

def upperUnip (F : Type) {a : Type} [Field F] [Fintype a] [DecidableEq a] (pos : a → ℕ) :
    Subgroup (GL a F) where
  carrier := {g | IsUpperUnip pos (g : Matrix a a F)}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun {g h} hg hh => Radical.Uni.mul (b := pos) hg hh
  inv_mem' := fun {g} hg => Radical.Uni.inv (b := pos) hg

theorem superSum_mul {pos : a → ℕ} {M M' : Matrix a a F} (h : IsUpperUnip pos M)
    (h' : IsUpperUnip pos M') : superSum pos (M * M') = superSum pos M + superSum pos M' := by
  unfold superSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with hs
  · exact Radical.Uni.mul_apply_succ (b := pos) h h' hs
  · simp

omit [DecidableEq a] in
theorem superSum_map {R : Type} [CommRing R] (f : R →+* F) (pos : a → ℕ) (M : Matrix a a R) :
    superSum pos (M.map f) = f (∑ r, ∑ s, if pos s = pos r + 1 then M r s else 0) := by
  unfold superSum
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp

noncomputable def genChar (φ : AddChar F Circle) (pos : a → ℕ) : upperUnip F pos →* ℂˣ :=
  Circle.toUnits.comp (MonoidHom.mk' (fun g => φ (superSum pos ((g : GL a F) : Matrix a a F)))
    (fun g h => by
      rw [← AddChar.map_add_eq_mul, ← superSum_mul g.2 h.2]
      rfl))

theorem genChar_apply (φ : AddChar F Circle) (pos : a → ℕ) (g : upperUnip F pos) :
    ((genChar φ pos g : ℂˣ) : ℂ) = φ (superSum pos ((g : GL a F) : Matrix a a F)) := rfl

end

theorem exists_isGenericLevel :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ϖ : kˣ, IsUnif ϖ → ∀ κ l : ℕ,
      ∃ P : TypeDatum k (Fin κ ⊕ Fin l), IsGenericLevel ψ ϖ P := by
  intro k _ _ _ _ ψ hψ ϖ hϖ κ l
  obtain ⟨φ, hφ⟩ := exists_residueChar hψ hϖ
  refine ⟨TypeDatum.ofResidue (upperUnip 𝓀[k] (framePos κ l)) (genChar φ (framePos κ l)), ?_, ?_⟩
  · intro g
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, ⟨u, rfl, rfl⟩, hu⟩
    · rintro ⟨gb, ⟨u, rfl, rfl⟩, hu⟩
      exact ⟨u, hu, rfl⟩
  · rintro ⟨g, u, hu, rfl⟩
    have h := TypeDatum.ofResidue_lam (upperUnip 𝓀[k] (framePos κ l)) (genChar φ (framePos κ l)) u hu
    rw [h, genChar_apply]
    have e1 := superSum_map (IsLocalRing.residue 𝒪[k]) (framePos κ l) (u : Matrix _ _ 𝒪[k])
    have e2 := superSum_map (algebraMap 𝒪[k] k) (framePos κ l) (u : Matrix _ _ 𝒪[k])
    have e3 := hφ (∑ r, ∑ s, if framePos κ l s = framePos κ l r + 1
      then (u : Matrix _ _ 𝒪[k]) r s else 0)
    rw [← e1] at e3
    have e4 : φ (superSum (framePos κ l) ((u : Matrix _ _ 𝒪[k]).map (IsLocalRing.residue 𝒪[k])))
        = ψ (((ϖ⁻¹ : kˣ) : k) *
          superSum (framePos κ l) ((u : Matrix _ _ 𝒪[k]).map (algebraMap 𝒪[k] k))) := by
      rw [e3, e2]
      rfl
    exact congrArg (fun z : Circle => (z : ℂ)) e4

end GlobalTheory.GenericLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSymmetricPositionLevel
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

noncomputable section
namespace GlobalTheory.SymLevelExists

section Plain
variable {F : Type} [Field F] {κ l : ℕ}

def symGroup (F : Type) [Field F] (κ l p : ℕ) : Subgroup (GL (Fin κ ⊕ Fin l) F) where
  carrier := {x | ∃ u ∈ N F (Fin κ) l p, ∃ γ : GL (Fin κ) F, IsUpperUnip Fin.val γ.val ∧ x = u * embX l γ}
  one_mem' := ⟨1, one_mem _, 1, fun _ _ _ => rfl, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨u, hu, γ, hγ, rfl⟩ ⟨u', hu', γ', hγ', rfl⟩
    refine ⟨_, mul_mem hu (Radical.conj_mem γ hu'), γ * γ',
      Radical.Uni.mul (b := Fin.val) hγ hγ', ?_⟩
    rw [map_mul]; group
  inv_mem' := by
    rintro _ ⟨u, hu, γ, hγ, rfl⟩
    refine ⟨_, Radical.conj_mem γ⁻¹ (inv_mem hu), γ⁻¹, Radical.Uni.inv (b := Fin.val) hγ, ?_⟩
    rw [map_inv]; group

theorem simpleSum_mul_embX (u : GL (Fin κ ⊕ Fin l) F) (γ : GL (Fin κ) F) :
    simpleSum (u * embX l γ) = simpleSum u := by
  have hv : ∀ i j, (u * embX l γ).val (Sum.inr i) (Sum.inr j) = u.val (Sum.inr i) (Sum.inr j) := by
    intro i j
    rw [Units.val_mul, Radical.embX_val, ← fromBlocks_toBlocks u.val]
    simp [fromBlocks_multiply]
  simp only [simpleSum, hv]

theorem toBlocks₁₁_mul_embX {p : ℕ} {u : GL (Fin κ ⊕ Fin l) F} (hu : u ∈ N F (Fin κ) l p) (γ : GL (Fin κ) F) :
    (u * embX l γ).val.toBlocks₁₁ = γ.val := by
  rw [Units.val_mul, Radical.embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks u.val]
  simp [fromBlocks_multiply, Radical.toBlocks₁₁_of_mem hu]

theorem superSum_mul {a : Type} [Fintype a] [DecidableEq a] {pos : a → ℕ} {M M' : Matrix a a F}
    (h : IsUpperUnip pos M) (h' : IsUpperUnip pos M') :
    superSum pos (M * M') = superSum pos M + superSum pos M' := by
  simp only [superSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · exact Radical.Uni.mul_apply_succ (b := pos) h h' hij
  · simp

def symSum (x : GL (Fin κ ⊕ Fin l) F) : F := simpleSum x + superSum Fin.val x.val.toBlocks₁₁

theorem symSum_eq {p : ℕ} {u : GL (Fin κ ⊕ Fin l) F} (hu : u ∈ N F (Fin κ) l p) (γ : GL (Fin κ) F) :
    symSum (u * embX l γ) = simpleSum u + superSum Fin.val γ.val := by
  rw [symSum, simpleSum_mul_embX, toBlocks₁₁_mul_embX hu]

theorem symSum_mul {p : ℕ} {x y : GL (Fin κ ⊕ Fin l) F} (hx : x ∈ symGroup F κ l p) (hy : y ∈ symGroup F κ l p) :
    symSum (x * y) = symSum x + symSum y := by
  obtain ⟨u, hu, γ, hγ, rfl⟩ := hx
  obtain ⟨u', hu', γ', hγ', rfl⟩ := hy
  have e : u * embX l γ * (u' * embX l γ') = u * (embX l γ * u' * (embX l γ)⁻¹) * embX l (γ * γ') := by
    rw [map_mul]; group
  rw [e, symSum_eq (mul_mem hu (Radical.conj_mem γ hu')), symSum_eq hu, symSum_eq hu',
    Radical.simpleSum_mul hu (Radical.conj_mem γ hu'), Radical.simpleSum_conj, Units.val_mul, superSum_mul hγ hγ']
  ring

end Plain

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_residue_char {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} (hϖ : IsUnif ϖ) :
    ∃ χ : 𝓀[k] → Circle, (∀ y z, χ (y + z) = χ y * χ z) ∧
      ∀ y : 𝒪[k], χ (IsLocalRing.residue 𝒪[k] y) = ψ ((ϖ⁻¹ : kˣ) * (y : k)) := by
  have hs : Function.Surjective (IsLocalRing.residue 𝒪[k]) := IsLocalRing.residue_surjective
  have key : ∀ y z : 𝒪[k], IsLocalRing.residue 𝒪[k] y = IsLocalRing.residue 𝒪[k] z →
      ψ ((ϖ⁻¹ : kˣ) * (y : k)) = ψ ((ϖ⁻¹ : kˣ) * (z : k)) := by
    intro y z h
    have h1 : valuation k ((y : k) - z) < 1 := (residue_eq_iff_lt y z).1 h
    have h2 := (hϖ _).1 h1
    have h3 : ψ ((ϖ⁻¹ : kˣ) * ((y : k) - z)) = 1 := by
      refine hψ.eq_one ?_
      have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
      simp only [cball, Set.mem_ofPred_eq, Units.val_one, map_one, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      rwa [inv_mul_le_one₀ h0]
    rw [show ((ϖ⁻¹ : kˣ) : k) * (y : k) = (ϖ⁻¹ : kˣ) * ((y : k) - z) + (ϖ⁻¹ : kˣ) * (z : k) by ring,
      AddChar.map_add_eq_mul, h3, one_mul]
  have h2 : ∀ y : 𝒪[k], ψ ((ϖ⁻¹ : kˣ) * ((Function.surjInv hs (IsLocalRing.residue 𝒪[k] y) : 𝒪[k]) : k)) =
      ψ ((ϖ⁻¹ : kˣ) * (y : k)) := fun y => key _ _ (Function.surjInv_eq hs _)
  refine ⟨fun y => ψ ((ϖ⁻¹ : kˣ) * ((Function.surjInv hs y : 𝒪[k]) : k)), fun y z => ?_, h2⟩
  obtain ⟨y, rfl⟩ := hs y
  obtain ⟨z, rfl⟩ := hs z
  beta_reduce
  rw [← map_add (f := _), h2, h2, h2, ← AddChar.map_add_eq_mul, ← mul_add]
  rfl

def symSumInt {κ l : ℕ} (g : GL (Fin κ ⊕ Fin l) 𝒪[k]) : 𝒪[k] :=
  (∑ i : Fin l, ∑ j : Fin l, if j.val = i.val + 1 then g.val (Sum.inr i) (Sum.inr j) else 0) +
    ∑ i : Fin κ, ∑ j : Fin κ, if j.val = i.val + 1 then g.val (Sum.inl i) (Sum.inl j) else 0

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem map_symSumInt {F : Type} [Field F] (f : 𝒪[k] →+* F) {κ l : ℕ} (g : GL (Fin κ ⊕ Fin l) 𝒪[k]) :
    f (symSumInt g) = symSum (Matrix.GeneralLinearGroup.map f g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [symSumInt, symSum, simpleSum, superSum, map_add (f := _), map_sum, apply_ite f, map_zero]
  rfl

end Local

theorem exists_isSymLevel :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ϖ : kˣ, IsUnif ϖ →
      ∀ ρ κ l : ℕ, ∃ P : GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l),
        GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsSymLevel ψ ϖ ρ P := by
  intro k _ _ _ _ ψ hψ ϖ hϖ ρ κ l
  obtain ⟨χ, hadd, hres⟩ := exists_residue_char hψ hϖ
  let χ' : symGroup 𝓀[k] κ l (ρ + 1) →* ℂˣ :=
    MonoidHom.mk' (fun x => Circle.toUnits (χ (symSum (x : GL (Fin κ ⊕ Fin l) 𝓀[k])))) fun x y => by
      rw [Subgroup.coe_mul, symSum_mul x.2 y.2, hadd, map_mul]
  refine ⟨TypeDatum.ofResidue _ χ', fun g => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨g₀, ⟨u, hu, γ, hγ, e⟩, rfl⟩
    exact ⟨u, hu, γ, hγ, g₀, rfl, e⟩
  · rintro ⟨u, hu, γ, hγ, g₀, rfl, e⟩
    exact ⟨g₀, ⟨u, hu, γ, hγ, e⟩, rfl⟩
  · rintro ⟨_, g₀, hg, rfl⟩
    rw [TypeDatum.ofResidue_lam _ χ' g₀ hg]
    change ((χ (symSum (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀)) : Circle) : ℂ) = _
    rw [← map_symSumInt, hres, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← mul_add]
    exact congrArg (fun z : k => ((ψ ((ϖ⁻¹ : kˣ) * z) : Circle) : ℂ)) (map_symSumInt (algebraMap 𝒪[k] k) g₀)

end GlobalTheory.SymLevelExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteQuotientCosetsScaledStandardLatticeBox
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.BoxCosets

theorem finite_cosets (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (c₁ c₂ : kˣ) :
    {yb : (n → k) ⧸ box n c₂ | ∃ y ∈ box n c₁, Submodule.Quotient.mk y = yb}.Finite := by
  have e : ∀ c : kˣ, (box n c : Set (n → k)) = Set.pi Set.univ (fun _ => cball c) := by
    intro c
    ext y
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    rfl
  have hc : IsCompact (box n c₁ : Set (n → k)) := by
    rw [e]; exact isCompact_univ_pi fun _ => isCompact_cball c₁
  have ho : IsOpen (box n c₂ : Set (n → k)) := by
    rw [e]; exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball c₂
  obtain ⟨t, -, ht⟩ := hc.elim_nhds_subcover
    (fun x => (fun y => y - x) ⁻¹' (box n c₂ : Set (n → k))) (by
      intro x _
      refine (ho.preimage (continuous_id.sub continuous_const)).mem_nhds ?_
      simp)
  refine (t.finite_toSet.image (fun x => (Submodule.Quotient.mk x : (n → k) ⧸ box n c₂))).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  have := ht hy
  simp only [Set.mem_iUnion] at this
  obtain ⟨x, hx, hxy⟩ := this
  exact ⟨x, hx, ((Submodule.Quotient.eq _).2 hxy).symm⟩

end GlobalTheory.BoxCosets
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatNeZeroOfMemR
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.FlatSourceStable

theorem om_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) {Φ : Matrix b a k → ℂ} (hΦ : Φ ≠ 0) : om μ g h Φ ≠ 0 := by
  intro h0
  apply hΦ
  have h1 := om_mul μ g⁻¹ g h⁻¹ h Φ
  rw [inv_mul_cancel, inv_mul_cancel, om_one, h0] at h1
  rw [h1]
  funext x
  simp [om]

theorem flat_ne_zero_of_mem_R : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ) (g : GL (n' ⊕ Fin (c + 1 + 1)) k) (h : GL (n ⊕ Fin (c + 1)) k), flat ψ ν μ Φ g h ≠ 0 → ∀ r ∈ R k n' (c + 1 + 1) 1, flat ψ ν μ Φ (r * g) h ≠ 0 := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ψ ν _ μ Φ g h h0 r hr
  obtain ⟨x, u, hu, rfl⟩ := GlobalTheory.RootEx.Radical.exists_of_mem_R hr
  unfold flat at h0 ⊢
  have e : om μ (embX (c + 1 + 1) x * u * g) h Φ =
      om μ (embX (c + 1 + 1) x) 1 (om μ u 1 (om μ g h Φ)) := by
    rw [← om_mul, ← om_mul, one_mul, one_mul]
  rw [e, (GlobalTheory.RootEx.opE_om_embX k n n' (c + 1) 1 le_rfl (by omega) ψ ν μ _).2 x,
    GlobalTheory.RootExSource.opE_om_source k n n' (c + 1) 1 le_rfl (by omega) ψ ν μ _ u hu]
  refine smul_ne_zero ?_ (om_ne_zero μ _ _ (smul_ne_zero (Circle.coe_ne_zero _) h0))
  exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (nabs_pos k _) _).ne'

end GlobalTheory.FlatSourceStable
end

