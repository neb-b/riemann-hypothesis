module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DSigma
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.dSigma :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (Y : Matrix (Fin n) (Fin n) F) (g : G), (∀ g, χ (D.σ g) = χ g) → dTw χ D.r Y (D.σ g) = (dTw χ D.r Yᵀ g)ᵀ := by
  intro F G _ _ n D χ Y g hχ
  have e1 : D.r (D.σ g) = (D.μ g : F) • (D.r g⁻¹)ᵀ := by
    have h : (D.r g⁻¹)ᵀ * (D.r g)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← map_mul, mul_inv_cancel, map_one, Matrix.transpose_one]
    calc D.r (D.σ g) = (D.r g⁻¹)ᵀ * ((D.r g)ᵀ * D.r (D.σ g)) := by
          rw [← Matrix.mul_assoc, h, Matrix.one_mul]
      _ = _ := by rw [D.form, Matrix.mul_smul, Matrix.mul_one]
  have e2 : D.r (D.σ g)⁻¹ = (D.μ g⁻¹ : F) • (D.r g)ᵀ := by
    have h : (D.r g)ᵀ * (D.r g⁻¹)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← map_mul, inv_mul_cancel, map_one, Matrix.transpose_one]
    rw [← map_inv]
    calc D.r (D.σ g⁻¹) = (D.r g)ᵀ * ((D.r g⁻¹)ᵀ * D.r (D.σ g⁻¹)) := by
          rw [← Matrix.mul_assoc, h, Matrix.one_mul]
      _ = _ := by rw [D.form, Matrix.mul_smul, Matrix.mul_one]
  have e3 : ((D.μ g : F) * D.μ g⁻¹) • (1 : Matrix (Fin n) (Fin n) F) = 1 := by
    have h : D.r (D.σ g) * D.r (D.σ g)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [e1, e2, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.transpose_mul, ← map_mul, mul_inv_cancel,
      map_one, Matrix.transpose_one, smul_smul] at h
    exact h
  have key : D.r (D.σ g) * Y * D.r (D.σ g)⁻¹ = (D.r g⁻¹)ᵀ * Y * (D.r g)ᵀ := by
    rw [e1, e2, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show ((D.μ g : F) * D.μ g⁻¹) • ((D.r g⁻¹)ᵀ * Y * (D.r g)ᵀ)
        = (((D.μ g : F) * D.μ g⁻¹) • (1 : Matrix (Fin n) (Fin n) F)) * ((D.r g⁻¹)ᵀ * Y * (D.r g)ᵀ) by
      rw [Matrix.smul_mul, Matrix.one_mul], e3, Matrix.one_mul]
  simp only [dTw, hχ, key, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DTwAlt
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.eigen :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (κ la : G → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F), TwCoc (fun _ => 1) D.r Set.univ κ → TwCoc D.χF D.r Set.univ la → (∀ g ∈ D.G', κ g + la g = dTw (fun _ => 1) D.r Y g) → (∃ Y₁, ∀ g ∈ D.G', κ g = dTw (fun _ => 1) D.r Y₁ g) ∧ ∃ Y₂, ∀ g ∈ D.G', la g = dTw (fun _ => 1) D.r Y₂ g := by
  intro F G _ _ n D κ la Y hκ hla hY
  set c : F := D.χF D.g₀ with hc
  have hc1 : c - 1 ≠ 0 := by
    intro h
    apply D.χ_ne
    ext
    exact sub_eq_zero.mp h
  set Z : Matrix (Fin n) (Fin n) F := D.r D.g₀ * Y * D.r D.g₀⁻¹ with hZ
  set Y₁ : Matrix (Fin n) (Fin n) F := (c - 1)⁻¹ • (c • Z - c • κ D.g₀ - la D.g₀ - Y) with hY₁
  have key : ∀ g ∈ D.G', κ g = dTw (fun _ => 1) D.r Y₁ g := by
    intro g hg
    have hg' : D.g₀⁻¹ * g * D.g₀ ∈ D.G' := by
      have := D.G'.mul_mem (D.comm D.g₀⁻¹ g) hg
      simpa using this
    set g' := D.g₀⁻¹ * g * D.g₀ with hgg
    have e : g * D.g₀ = D.g₀ * g' := by rw [hgg]; group
    have e' : g'⁻¹ * D.g₀⁻¹ = D.g₀⁻¹ * g⁻¹ := by rw [hgg]; group
    have h1 := hκ g trivial D.g₀ trivial
    have h2 := hla g trivial D.g₀ trivial
    rw [e, hκ D.g₀ trivial g' trivial] at h1
    rw [e, hla D.g₀ trivial g' trivial] at h2
    have hχ : D.χF g = 1 := by simp [DetFr.χF, D.χ_triv g hg]
    rw [hχ, ← hc] at h2
    have h3 := hY g hg
    have h4 : D.r D.g₀ * κ g' * D.r D.g₀⁻¹ + D.r D.g₀ * la g' * D.r D.g₀⁻¹
        = D.r g * Z * D.r g⁻¹ - Z := by
      rw [← add_mul, ← mul_add, hY g' hg', dTw, one_smul, mul_sub, sub_mul, hZ]
      congr 1
      calc D.r D.g₀ * (D.r g' * Y * D.r g'⁻¹) * D.r D.g₀⁻¹
          = (D.r D.g₀ * D.r g') * Y * (D.r g'⁻¹ * D.r D.g₀⁻¹) := by simp only [mul_assoc]
        _ = (D.r g * D.r D.g₀) * Y * (D.r D.g₀⁻¹ * D.r g⁻¹) := by
          rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, e, e']
        _ = _ := by simp only [mul_assoc]
    have h5 : (c - 1) • κ g = (c - 1) • dTw (fun _ => 1) D.r Y₁ g := by
      simp only [dTw, one_smul] at h1 h2 h3 ⊢
      rw [hY₁, smul_sub, mul_smul_comm, smul_mul_assoc, smul_inv_smul₀ hc1, smul_inv_smul₀ hc1]
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
      linear_combination (norm := module) c • h4 - c • h1 - h2 - h3
    exact smul_right_injective _ hc1 h5
  refine ⟨⟨Y₁, key⟩, Y - Y₁, fun g hg => ?_⟩
  have h3 := hY g hg
  rw [key g hg] at h3
  simp only [dTw, one_smul, mul_sub, sub_mul] at h3 ⊢
  rw [← sub_eq_zero] at h3 ⊢
  rw [← h3]; abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DerEv
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem single_mem_ev_of_same_block {F : Type} [CommRing F] {n a : ℕ} (p q : Fin n) (c : F)
    (h : ((p : ℕ) < a ↔ (q : ℕ) < a)) : Matrix.single p q c ∈ Ev F F n a := by
  intro i j
  refine ⟨fun _ => Submodule.mem_top, fun hij => ?_⟩
  rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hij h

theorem UpperTheory.V.Pa.Det.derEv :
    ∀ {F : Type} [CommRing F] {n a : ℕ} (d : Matrix (Fin n) (Fin n) F →ₗ[F] Matrix (Fin n) (Fin n) F), (∀ x ∈ Ev F F n a, ∀ y ∈ Ev F F n a, d (x * y) = d x * y + x * d y) → ∃ Y, ∀ x ∈ Ev F F n a, d x = Y * x - x * Y := by
  intro F _ n a d hd
  let β : Fin n → Fin n := fun i =>
    if h : (i : ℕ) < a then ⟨0, lt_of_le_of_lt (Nat.zero_le _) i.isLt⟩
    else ⟨a, lt_of_le_of_lt (not_lt.mp h) i.isLt⟩
  have hβ : ∀ i : Fin n, ((i : ℕ) < a ↔ (β i : ℕ) < a) := by
    intro i
    by_cases h : (i : ℕ) < a
    · simp only [β, dif_pos h]
      exact ⟨fun _ => Nat.zero_lt_of_lt h, fun _ => h⟩
    · simp only [β, dif_neg h]
      exact ⟨fun h' => absurd h' h, fun h' => absurd h' (lt_irrefl _)⟩
  have hβeq : ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) → β i = β j := by
    intro i j h
    by_cases hi : (i : ℕ) < a
    · have hj := h.mp hi
      simp only [β, dif_pos hi, dif_pos hj]
    · have hj : ¬ (j : ℕ) < a := fun hj => hi (h.mpr hj)
      simp only [β, dif_neg hi, dif_neg hj]
  let E : Fin n → Fin n → Matrix (Fin n) (Fin n) F := fun i j => Matrix.single i j 1
  let u : Fin n → Matrix (Fin n) (Fin n) F := fun k => E k (β k)
  let v : Fin n → Matrix (Fin n) (Fin n) F := fun k => E (β k) k
  have hu : ∀ k, u k ∈ Ev F F n a := fun k => single_mem_ev_of_same_block _ _ _ (hβ k)
  let Y := ∑ k, d (u k) * v k
  have hsum : ∑ k, u k * v k = 1 := by
    simp only [u, v, E, Matrix.single_mul_single_same, mul_one]
    exact Matrix.sum_single_one
  have key : ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) →
      d (E i j) = Y * E i j - E i j * Y := by
    intro i j hij
    have hE : E i j ∈ Ev F F n a := single_mem_ev_of_same_block i j 1 hij
    have h1 : Y * E i j = d (u i) * v j := by
      simp only [Y, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_eq_single i]
      · simp only [v, E, u]
        rw [Matrix.single_mul_single_same, mul_one, hβeq i j hij]
      · intro k _ hk
        simp only [v, E]
        rw [Matrix.single_mul_single_of_ne _ _ _ _ hk _, mul_zero]
      · simp
    have hk : ∀ k, E i j * d (u k) = d (E i j * u k) - d (E i j) * u k := by
      intro k
      rw [hd _ hE _ (hu k)]
      abel
    have hEu : ∀ k, E i j * u k = if j = k then u i else 0 := by
      intro k
      split_ifs with h
      · subst h
        simp only [E, u]
        rw [Matrix.single_mul_single_same, mul_one, hβeq i j hij]
      · exact Matrix.single_mul_single_of_ne _ _ _ _ h _
    have h2 : E i j * Y = d (u i) * v j - d (E i j) := by
      calc E i j * Y = ∑ k, (d (E i j * u k) * v k - d (E i j) * (u k * v k)) := by
            simp only [Y, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← mul_assoc, hk, sub_mul, mul_assoc]
        _ = d (u i) * v j - d (E i j) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_one]
            congr 1
            rw [Finset.sum_eq_single j]
            · rw [hEu, if_pos rfl]
            · intro k _ hk
              rw [hEu, if_neg (Ne.symm hk), map_zero, zero_mul]
            · simp
    rw [h1, h2]
    abel
  refine ⟨Y, fun x hx => ?_⟩
  let D' : Matrix (Fin n) (Fin n) F →ₗ[F] Matrix (Fin n) (Fin n) F :=
    d - (LinearMap.mulLeft F Y - LinearMap.mulRight F Y)
  have hD : D' x = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.matrix_eq_sum_single x, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hij : ((i : ℕ) < a ↔ (j : ℕ) < a)
    · have hs : Matrix.single i j (x i j) = x i j • E i j := by
        simp only [E, Matrix.smul_single, smul_eq_mul, mul_one]
      rw [hs, map_smul]
      simp only [D', LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        key i j hij, sub_self, smul_zero]
    · have h0 : x i j = 0 := (Submodule.mem_bot F).mp ((hx i j).2 hij)
      rw [h0, Matrix.single_zero, map_zero]
  simp only [D', LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    sub_eq_zero] at hD
  exact hD
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.EllClosed
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section
variable {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S}

private theorem ac_const (c : R) : AdicCont I fun _ : Γ => c := fun _ => IsLocallyConstant.const _

private theorem ac_add {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s + g s := by
  intro N
  have := (hf N).comp₂ (hg N) (· + ·)
  simpa [Function.comp_def, map_add (f := _)] using this

private theorem ac_mul {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s * g s := by
  intro N
  have := (hf N).comp₂ (hg N) (· * ·)
  simpa [Function.comp_def, map_mul] using this

private theorem ac_sum {ι : Type} (T : Finset ι) {f : ι → Γ → R} (hf : ∀ i, AdicCont I (f i)) :
    AdicCont I fun s => ∑ i ∈ T, f i s := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using ac_const (I := I) (Γ := Γ) 0
  | insert a T ha ih => simpa only [Finset.sum_insert ha] using ac_add (hf a) ih

private theorem ac_map (L : R → S) (hL : ∀ (N : ℕ) a b, a - b ∈ I ^ N → L a - L b ∈ J ^ N) {f : Γ → R}
    (hf : AdicCont I f) : AdicCont J fun s => L (f s) := by
  intro N
  have h : IsLocallyConstant fun s => Ideal.Quotient.mk (I ^ N) (f s) := hf N
  show IsLocallyConstant fun s => Ideal.Quotient.mk (J ^ N) (L (f s))
  rw [IsLocallyConstant.iff_eventually_eq] at h ⊢
  intro x
  filter_upwards [h x] with y hy
  rw [Ideal.Quotient.eq] at hy ⊢
  exact hL N _ _ hy

private theorem ac_hom (L : R →+* S) (t : R) {f : Γ → R}
    (hf : AdicCont (Ideal.span {t}) f) : AdicCont (Ideal.span {L t}) fun s => L (f s) := by
  refine ac_map L (fun N a b h => ?_) hf
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h ⊢
  obtain ⟨c, hc⟩ := h
  exact ⟨L c, by rw [← map_pow, ← map_mul, hc, map_sub]⟩

private theorem ac_eta {g : ℕ} (t : R) {f : Γ → DD R g}
    (hf : AdicCont (Ideal.span {(DD.C t : DD R g)}) f) : AdicCont (Ideal.span {t}) fun s => (f s).eta := by
  refine ac_map (fun x : DD R g => x.eta) (fun N a b h => ?_) hf
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  obtain ⟨c, hc⟩ := h
  refine ⟨c.eta, ?_⟩
  have e : (a - b).eta = a.eta - b.eta := rfl
  rw [← e, ← hc, ← map_pow, show (DD.C (t ^ N) : DD R g) = ⟨t ^ N, 0, 0, 0⟩ from rfl]
  simp

private theorem sum_comp {g : ℕ} {ι : Type} (T : Finset ι) (f : ι → DD R g) :
    (∑ i ∈ T, f i).a = ∑ i ∈ T, (f i).a ∧ (∀ j, (∑ i ∈ T, f i).ep j = ∑ i ∈ T, (f i).ep j) ∧
      (∀ j, (∑ i ∈ T, f i).ep' j = ∑ i ∈ T, (f i).ep' j) ∧ (∑ i ∈ T, f i).eta = ∑ i ∈ T, (f i).eta := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨rfl, fun _ => rfl, fun _ => rfl, rfl⟩
  | insert i T hi ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [Finset.sum_insert hi]
    exact ⟨by rw [← h1]; rfl, fun j => by rw [← h2 j]; rfl, fun j => by rw [← h3 j]; rfl, by rw [← h4]; rfl⟩

private theorem epM_eq {g n : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) R) (a b : Fin n) :
    DD.epM Z a b = ∑ j, DD.C (Z j a b) * (⟨0, Pi.single j 1, 0, 0⟩ : DD R g) := by
  classical
  have hC : ∀ c : R, (DD.C c : DD R g) = ⟨c, 0, 0, 0⟩ := fun _ => rfl
  obtain ⟨h1, h2, h3, h4⟩ := sum_comp Finset.univ (fun j => DD.C (Z j a b) * (⟨0, Pi.single j 1, 0, 0⟩ : DD R g))
  apply DD.ext
  · rw [h1]
    change (0 : R) = _
    simp [hC]
  · funext j
    rw [h2 j]
    change Z j a b = _
    simp [hC, Pi.single_apply]
  · funext j
    rw [h3 j]
    change (0 : R) = _
    simp [hC]
  · rw [h4]
    change (0 : R) = _
    simp [hC]

end

theorem UpperTheory.V.Pa.Det.ellClosed :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (z : F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)), z ∈ TwZ k x.A → IsClosed {σ : F.G₀ | ell k x.A σ z = 0} := by
  intro l _ F n x k z hz
  unfold TwZ at hz
  obtain ⟨-, hzc, -, -⟩ := hz
  have hmul : ∀ M N : F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g),
      (∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => M s i j) →
      (∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => N s i j) →
      ∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => (M s * N s) i j := by
    intro M N hM hN i j
    simp only [Matrix.mul_apply]
    exact ac_sum _ fun m => ac_mul (hM i m) (hN m j)
  have hρ : ∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => x.ρX (DD x.A k.g) s i j := by
    intro i j
    have h := x.cont i j
    rw [PowerSeries.maximalIdeal_eq_span_X] at h
    exact ac_hom DD.C x.t h
  have hκ : ∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)})
      fun s => DD.epM (fun m => (k.κ m s).map ⇑(algebraMap x.A x.A)) i j := by
    intro i j
    simp only [epM_eq]
    refine ac_sum _ fun m => ac_mul ?_ (ac_const _)
    have hm := k.mem m
    unfold SelZ at hm
    obtain ⟨-, hc, -⟩ := hm
    exact ac_hom DD.C x.t (hc i j)
  have hρ1 : ∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => k.ρ1 x.A s i j := by
    have := hmul (fun s => 1 + DD.epM fun m => (k.κ m s).map ⇑(algebraMap x.A x.A))
      (fun s => x.ρX (DD x.A k.g) s)
      (fun i j => by simpa only [Matrix.add_apply] using ac_add (ac_const _) (hκ i j)) hρ
    intro i j
    exact this i j
  have hprod := hmul z (fun s => k.ρ1 x.A s) hzc hρ1
  have htr : AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => (z s * k.ρ1 x.A s).trace := by
    simp only [Matrix.trace, Matrix.diag]
    exact ac_sum _ fun i => hprod i i
  have hf : AdicCont (Ideal.span {x.t}) fun s => ell k x.A s z := ac_eta x.t htr
  have sep : ∀ a : x.A, (∀ N : ℕ, Ideal.Quotient.mk (Ideal.span {x.t} ^ N) a = 0) → a = 0 := by
    intro a ha
    refine PowerSeries.ext fun m => ?_
    have h := ha (m + 1)
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
    obtain ⟨c, hc⟩ := h
    rw [show x.t = PowerSeries.X from rfl] at hc
    rw [← hc, PowerSeries.coeff_mul_X_pow']
    simp
  have hset : {σ : F.G₀ | ell k x.A σ z = 0} =
      ⋂ N : ℕ, {s | Ideal.Quotient.mk (Ideal.span {x.t} ^ N) (ell k x.A s z) = 0} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h N
      rw [h, map_zero]
    · exact sep _
  rw [hset]
  exact isClosed_iInter fun N =>
    ((show IsLocallyConstant fun s => Ideal.Quotient.mk (Ideal.span {x.t} ^ N) (ell k x.A s z) from hf N).isClopen_fiber 0).isClosed
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ExistsIntegralBlockIwasawaDecomposition
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.exists_integral_block_iwasawa_decomposition :
    ∀ {A F : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field F] [Algebra A F] [IsFractionRing A F] {n : ℕ} (bl ty : Fin n → Bool) (g : GL (Fin n) F), (∀ i j, bl i ≠ ty j → g i j = 0) → ∃ (w : GL (Fin n) A) (b : GL (Fin n) F), (∀ i j, j < i → b i j = 0) ∧ GeneralLinearGroup.map (algebraMap A F) w = g * b ∧ ∀ i j, bl i ≠ ty j → w i j = 0 := by
  intro A F _ _ _ _ _ _ n bl ty g hg
  obtain ⟨k, b0, hb0, hgkb⟩ := GlobalTheory.ValIwasawa.iwasawa A F n g
  haveI : Invertible (b0 : Matrix (Fin n) (Fin n) F) := Units.invertible b0
  have hctri : ((b0 : Matrix (Fin n) (Fin n) F)⁻¹).BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular hb0
  set c : Matrix (Fin n) (Fin n) F := (b0 : Matrix (Fin n) (Fin n) F)⁻¹ with hcdef
  have hgc : (g : Matrix (Fin n) (Fin n) F) * c = (GeneralLinearGroup.map (algebraMap A F) k : Matrix (Fin n) (Fin n) F) := by
    have h1 : g * b0⁻¹ = GeneralLinearGroup.map (algebraMap A F) k := mul_inv_eq_iff_eq_mul.mpr hgkb
    have h2 := congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) h1
    simpa [Units.val_mul, Matrix.coe_units_inv, hcdef] using h2
  let c' : Matrix (Fin n) (Fin n) F := Matrix.of fun i j => if ty i = ty j then c i j else 0
  have hc'tri : c'.BlockTriangular id := by
    intro i j hij
    simp only [c', Matrix.of_apply]
    split_ifs
    · exact hctri hij
    · rfl
  have hgc' : ∀ i j, ((g : Matrix (Fin n) (Fin n) F) * c') i j = if bl i = ty j then algebraMap A F ((k : Matrix (Fin n) (Fin n) A) i j) else 0 := by
    intro i j
    rw [Matrix.mul_apply]
    split_ifs with hij
    · rw [← GeneralLinearGroup.map_apply, ← hgc, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [c', Matrix.of_apply]
      split_ifs with hl
      · rfl
      · rw [hg i l (fun h => hl (h.symm.trans hij)), zero_mul, zero_mul]
    · refine Finset.sum_eq_zero fun l _ => ?_
      simp only [c', Matrix.of_apply]
      split_ifs with hl
      · rw [hg i l (fun h => hij (h.trans hl)), zero_mul]
      · rw [mul_zero]
  let kw : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => if bl i = ty j then (k : Matrix (Fin n) (Fin n) A) i j else 0
  have hmap : (algebraMap A F).mapMatrix kw = (g : Matrix (Fin n) (Fin n) F) * c' := by
    ext i j
    rw [hgc' i j]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, kw, Matrix.of_apply]
    split_ifs
    · rfl
    · exact map_zero _
  have hdetc : c'.det = c.det := by
    rw [Matrix.det_of_upperTriangular hc'tri, Matrix.det_of_upperTriangular hctri]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [c']
  have hcunit : IsUnit c.det := by
    have := Matrix.isUnits_det_units b0⁻¹
    rwa [Matrix.coe_units_inv] at this
  have hc'unit : IsUnit c'.det := hdetc ▸ hcunit
  have hdetk : kw.det = (k : Matrix (Fin n) (Fin n) A).det := by
    apply IsFractionRing.injective A F
    rw [RingHom.map_det, RingHom.map_det, hmap, Matrix.det_mul, hdetc, ← Matrix.det_mul, hgc]
    rfl
  have hkunit : IsUnit kw.det := hdetk ▸ Matrix.isUnits_det_units k
  refine ⟨GeneralLinearGroup.mk'' kw hkunit, GeneralLinearGroup.mk'' c' hc'unit, ?_, ?_, ?_⟩
  · intro i j hij
    exact hc'tri hij
  · apply Units.ext
    rw [Units.val_mul]
    exact hmap
  · intro i j hij
    show kw i j = 0
    simp [kw, hij]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ExtFree
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.extFree :
    ∀ {K K' : Type} [Field K] [Field K'] (j : PowerSeries K →+* PowerSeries K'), Function.Injective j → IsLocalHom j → j.Finite → ∃ (m : ℕ) (b : Fin m → PowerSeries K') (p : Fin m → PowerSeries K' →+ PowerSeries K), 0 < m ∧ (∀ y, y = ∑ i, j (p i y) * b i) ∧ (∀ i a y, p i (j a * y) = a * p i y) ∧ (∀ i i', p i (b i') = if i = i' then (1 : PowerSeries K) else 0) ∧ (∀ N : ℕ, ∃ N' : ℕ, ∀ y ∈ Ideal.span {(PowerSeries.X : PowerSeries K')} ^ N', ∀ i, p i y ∈ Ideal.span {(PowerSeries.X : PowerSeries K)} ^ N) ∧ ∃ (e : ℕ) (u : (PowerSeries K')ˣ), 0 < e ∧ j PowerSeries.X = (u : PowerSeries K') * (PowerSeries.X : PowerSeries K') ^ e := by
  intro K K' _ _ j hi hl hf
  letI : Algebra (PowerSeries K) (PowerSeries K') := j.toAlgebra
  haveI : Module.Finite (PowerSeries K) (PowerSeries K') := hf
  haveI : FaithfulSMul (PowerSeries K) (PowerSeries K') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hi
  haveI : Module.Free (PowerSeries K) (PowerSeries K') := Module.free_of_finite_type_torsion_free'
  let B := Module.finBasis (PowerSeries K) (PowerSeries K')
  have hsm : ∀ (a : PowerSeries K) (y : PowerSeries K'), j a * y = a • y := fun a y => rfl
  have hX : ∃ (e : ℕ) (u : (PowerSeries K')ˣ), 0 < e ∧
      j PowerSeries.X = (u : PowerSeries K') * (PowerSeries.X : PowerSeries K') ^ e := by
    have h0 : j PowerSeries.X ≠ 0 := by
      intro h
      exact PowerSeries.X_ne_zero (hi (h.trans (map_zero j).symm))
    obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 (PowerSeries.X_irreducible (R := K'))
    refine ⟨e, v⁻¹, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos e with h | h
      · exfalso
        rw [h, pow_zero] at hv
        have hu : IsUnit (j PowerSeries.X) := IsUnit.of_mul_eq_one _ hv
        exact (PowerSeries.X_irreducible (R := K)).not_isUnit (isUnit_of_map_unit j _ hu)
      · exact h
    · rw [← hv, mul_left_comm, Units.inv_mul, mul_one]
  obtain ⟨e, u, he, hu⟩ := hX
  refine ⟨Module.finrank (PowerSeries K) (PowerSeries K'), fun i => B i, fun i => (B.coord i).toAddMonoidHom,
    Module.finrank_pos, ?_, ?_, ?_, ?_, e, u, he, hu⟩
  · intro y
    conv_lhs => rw [← B.sum_repr y]
    rfl
  · intro i a y
    show B.coord i (j a * y) = a * B.coord i y
    rw [hsm, LinearMap.map_smul, smul_eq_mul]
  · intro i i'
    show B.repr (B i') i = _
    rw [B.repr_self_apply]
    by_cases h : i = i'
    · subst h
      simp
    · simp [h, Ne.symm h]
  · intro N
    refine ⟨e * N, fun y hy i => ?_⟩
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy ⊢
    obtain ⟨z, rfl⟩ := hy
    have hu1 : (u : PowerSeries K') ^ N * ((u⁻¹ : (PowerSeries K')ˣ) : PowerSeries K') ^ N = 1 := by
      rw [← mul_pow, Units.mul_inv, one_pow]
    have hz : (PowerSeries.X : PowerSeries K') ^ (e * N) * z =
        j (PowerSeries.X ^ N) * (((u⁻¹ : (PowerSeries K')ˣ) : PowerSeries K') ^ N * z) := by
      rw [map_pow, hu, pow_mul]
      linear_combination (-(((PowerSeries.X : PowerSeries K') ^ e) ^ N * z)) * hu1
    refine ⟨B.coord i (((u⁻¹ : (PowerSeries K')ˣ) : PowerSeries K') ^ N * z), ?_⟩
    show B.coord i _ = _
    rw [hz, hsm, LinearMap.map_smul, smul_eq_mul]
end

