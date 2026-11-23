module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsBasePointDerivationOfWeightHomogeneous
section
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

private theorem coeff_single_mul {E σ : Type} [CommRing E] (i : σ) (f g : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
      MvPowerSeries.constantCoeff g * MvPowerSeries.coeff (Finsupp.single i 1) f := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, mul_comm]

private theorem free_ext {O σ Q : Type} [CommRing O] [Fintype σ] [AddCommGroup Q] [Module O Q]
    (D E : MvPowerSeries σ O →ₗ[O] Q)
    (hD : ∀ f g, D (f * g) = MvPowerSeries.constantCoeff f • D g + MvPowerSeries.constantCoeff g • D f)
    (hE : ∀ f g, E (f * g) = MvPowerSeries.constantCoeff f • E g + MvPowerSeries.constantCoeff g • E f)
    (hX : ∀ s, D (MvPowerSeries.X s) = E (MvPowerSeries.X s)) (f : MvPowerSeries σ O) : D f = E f := by
  let W' := WPres.free O (fun _ : σ => (0 : ℤ))
  have h' : W'.HasOrigin := fun f hf => by
    have : f = 0 := hf
    rw [this, map_zero]
  have ho : ∀ f, W'.origin h' f = MvPowerSeries.constantCoeff f := fun f => W'.origin_π h' f
  have h0 := (der_extend O _ ℤ W' h' Q).2 (D - E) (fun f g => by
    rw [ho, ho]
    simp only [LinearMap.sub_apply]
    rw [hD, hE, smul_sub, smul_sub]
    abel) (fun (s : σ) => by
    show D (MvPowerSeries.X s) - E (MvPowerSeries.X s) = 0
    rw [hX, sub_self])
  rw [sub_eq_zero.1 h0]

private theorem free_ex {O σ : Type} [CommRing O] [Fintype σ] (d : σ → O) :
    ∃ L : MvPowerSeries σ O →ₗ[O] O,
      (∀ f g, L (f * g) = MvPowerSeries.constantCoeff f • L g + MvPowerSeries.constantCoeff g • L f) ∧
      (∀ s, L (MvPowerSeries.X s) = d s) ∧
      ∀ f, L f = ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f • d s := by
  classical
  let L : MvPowerSeries σ O →ₗ[O] O :=
    ∑ s, (MvPowerSeries.coeff (Finsupp.single s 1) : MvPowerSeries σ O →ₗ[O] O).smulRight (d s)
  have hL : ∀ f, L f = ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f • d s := fun f => by
    simp [L]
  refine ⟨L, fun f g => ?_, fun s => ?_, hL⟩
  · rw [hL, hL, hL]
    simp only [coeff_single_mul, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  · rw [hL]
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj]

theorem UpperTheory.exists_base_pointDerivation_of_weight_homogeneous :
    ∀ {O B R S Q : Type} [CommRing O] [CommRing B] [Algebra O B] [CommRing R] [Algebra O R] [CommRing S] [Algebra O S] [AddCommGroup Q] [Module O Q]
          (WB : WPres O ℤ B) (hB : WB.HasOrigin) (W : WPres O ℤ R) (h : W.HasOrigin) {τ : Type} (e : WB.σ ⊕ τ ≃ W.σ), (∀ s, W.wt (e (.inl s)) = WB.wt s) →
          RingHom.ker W.π = (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)) →
          ∀ (qh : R →ₐ[O] S) (x₀ : S →ₐ[O] O), x₀.comp qh = W.origin h → ∀ (p : O →ₗ[O] Q), Function.Surjective p → ∀ (j : ℤ),
          ∀ D ∈ PtDer x₀ Q, (∀ s, W.wt s ≠ j → D (qh (W.z s)) = 0) → ∀ D₁ ∈ PtDer (WB.origin hB) O, (∀ s, WB.wt s ≠ j → D₁ (WB.z s) = 0) →
          (∀ s, p (D₁ (WB.z s)) = D (qh (W.z (e (.inl s))))) →
          ∃ D' ∈ PtDer (W.originA h) O, HasWt W.gr j D' ∧ ∀ f : W.A, D (qh f) = p (D' f) := by
  intro O B R S Q _ _ _ _ _ _ _ _ _ WB hB W h τ e hwt hker qh x₀ hx p hp j D hD hDw D₁ hD₁ hD₁w hpD
  classical
  have hd : ∀ s : W.σ, ∃ d : O, (∀ t, s = e (.inl t) → d = D₁ (WB.z t)) ∧ (W.wt s ≠ j → d = 0) ∧
      p d = D (qh (W.z s)) := fun s => by
    obtain ⟨u, rfl⟩ := e.surjective s
    rcases u with t | t
    · refine ⟨D₁ (WB.z t), fun t' ht => ?_, fun hj => hD₁w t (by rwa [← hwt]), hpD t⟩
      rw [Sum.inl.inj (e.injective ht)]
    · by_cases hj : W.wt (e (.inr t)) = j
      · obtain ⟨a, ha⟩ := hp (D (qh (W.z (e (.inr t)))))
        exact ⟨a, fun t' ht => absurd (e.injective ht) Sum.inr_ne_inl, fun h' => absurd hj h', ha⟩
      · exact ⟨0, fun t' ht => absurd (e.injective ht) Sum.inr_ne_inl, fun _ => rfl,
          by rw [map_zero, hDw _ hj]⟩
  choose d hd1 hd2 hd3 using hd
  obtain ⟨L, hL, hLX, hLs⟩ := free_ex d
  have hren : ∀ g, L (MvPowerSeries.rename (fun s => e (.inl s)) g) = D₁ (WB.π g) :=
    free_ext (L ∘ₗ (MvPowerSeries.rename (fun s => e (.inl s)) : MvPowerSeries WB.σ O →ₐ[O] _).toLinearMap)
      (D₁ ∘ₗ WB.π.toLinearMap)
      (fun f g => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, hL,
          MvPowerSeries.constantCoeff_rename])
      (fun f g => by
        have h1 : D₁ (WB.π f * WB.π g) = _ := hD₁ _ _
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, h1, WB.origin_π])
      (fun s => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPowerSeries.rename_X, hLX]
        exact hd1 _ s rfl)
  have hk : ∀ f, W.π f = 0 → L f = 0 := fun f hf => by
    have hf' : f ∈ RingHom.ker W.π := hf
    have key : ∀ f ∈ (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)), L f = 0 := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, hg, rfl⟩ := hx
        have hg' : WB.π g = 0 := hg
        rw [hren, hg', map_zero]
      | zero => exact map_zero L
      | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
      | smul a x hx hx' =>
        have : x ∈ RingHom.ker W.π := by rw [hker]; exact hx
        rw [smul_eq_mul, hL, hx', h x this, smul_zero, zero_smul, add_zero]
    exact key f (hker ▸ hf')
  have hs : Function.Surjective W.π.toLinearMap := W.surj
  let E : R →ₗ[O] O := ((LinearMap.ker W.π.toLinearMap).liftQ L (fun f hf => hk f hf)) ∘ₗ
    (W.π.toLinearMap.quotKerEquivOfSurjective hs).symm.toLinearMap
  have hE : ∀ f, E (W.π f) = L f := fun f => by
    have : (W.π.toLinearMap.quotKerEquivOfSurjective hs).symm (W.π f) = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show (LinearMap.ker W.π.toLinearMap).liftQ L (fun f hf => hk f hf)
      ((W.π.toLinearMap.quotKerEquivOfSurjective hs).symm (W.π f)) = _
    rw [this]
    rfl
  have hEd : ∀ a b, E (a * b) = W.origin h a • E b + W.origin h b • E a := fun a b => by
    obtain ⟨f, rfl⟩ := W.surj a
    obtain ⟨g, rfl⟩ := W.surj b
    rw [← map_mul, hE, hE, hE, hL, W.origin_π, W.origin_π]
  have hxo : ∀ f, x₀ (qh (W.π f)) = MvPowerSeries.constantCoeff f := fun f => by
    rw [← AlgHom.comp_apply, hx, W.origin_π]
  have hred : ∀ f, D (qh (W.π f)) = p (L f) :=
    free_ext (D ∘ₗ (qh.comp W.π).toLinearMap) (p ∘ₗ L)
      (fun f g => by
        have h1 : D (qh (W.π f) * qh (W.π g)) = _ := hD _ _
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, map_mul, h1, hxo])
      (fun f g => by simp only [LinearMap.comp_apply, hL, map_add (f := _), map_smul])
      (fun s => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, hLX, hd3]
        rfl)
  refine ⟨E ∘ₗ W.A.val.toLinearMap, fun a b => hEd a b, fun i hi a ha => ?_, fun a => ?_⟩
  · obtain ⟨f, hf, hfa⟩ := ha
    have hfa' : W.π f = (a : R) := hfa
    show E (a : R) = 0
    rw [← hfa', hE, hLs]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hs : W.wt s = j
    · rw [hf (Finsupp.single s 1) (by simpa [Finsupp.weight_single, hs] using hi.symm), zero_smul]
    · rw [hd2 s hs, smul_zero]
  · obtain ⟨f, hf⟩ := W.surj (a : R)
    show D (qh (a : R)) = p (E (a : R))
    rw [← hf, hE, hred]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsEqnsOfWeightedGenerators
section
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

theorem UpperTheory.exists_eqns_of_weighted_generators :
    ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) (x : A →ₐ[O] O) (r s r' s' m : ℕ) {κ : Type} [Finite κ] (g : κ → A) (w : κ → ℤ),
          (∀ i, g i ∈ 𝒜 (w i)) → (∀ i, x (g i) = 0) → (∀ i, -2 ≤ w i ∧ w i ≤ 2) →
          Nat.card {i // w i = -1} = r + 1 → Nat.card {i // w i = -2} = s → Nat.card {i // w i = 1} = r' → Nat.card {i // w i = 2} = s' → Nat.card {i // w i = 0} = m →
          ∃ Q : Eqns 𝒜 x r s r' s' m, Q.ideal = Ideal.span (Set.range g) := by
  intro O A _ _ _ 𝒜 x r s r' s' m κ _ g w hg hx hw h1 h2 h3 h4 h5
  have key : ∀ (j : ℤ) (n : ℕ), Nat.card {i // w i = j} = n →
      ∃ F : Fin n → A, (∀ k, F k ∈ 𝒜 j ∧ x (F k) = 0) ∧ Set.range F = g '' {i | w i = j} := by
    intro j n hn
    let e := Finite.equivFinOfCardEq hn
    refine ⟨fun k => g (e.symm k).1, fun k => ⟨?_, hx _⟩, ?_⟩
    · have := hg (e.symm k).1
      rwa [(e.symm k).2] at this
    · ext a
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨(e.symm k).1, (e.symm k).2, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨e ⟨i, hi⟩, by simp⟩
  obtain ⟨F, hF, rF⟩ := key _ _ h1
  obtain ⟨G, hG, rG⟩ := key _ _ h2
  obtain ⟨E, hE, rE⟩ := key _ _ h3
  obtain ⟨E', hE', rE'⟩ := key _ _ h4
  obtain ⟨Z, hZ, rZ⟩ := key _ _ h5
  refine ⟨⟨F, G, E, E', Z, fun i => (hF i).1, fun i => (hG i).1, fun i => (hE i).1, fun i => (hE' i).1, hZ⟩, ?_⟩
  show Ideal.span (Set.range F ∪ Set.range G ∪ Set.range E ∪ Set.range E' ∪ Set.range Z) = _
  rw [rF, rG, rE, rE', rZ, ← Set.image_union, ← Set.image_union, ← Set.image_union, ← Set.image_union,
    ← Set.image_univ]
  congr 2
  ext i
  have := hw i
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsOriginAndChartOfIsLocPres
section
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

private theorem lc_wcomp_mul (O : Type) [CommRing O] {σ X : Type} [AddCommGroup X] (wt : σ → X)
    {w : X} {e : MvPowerSeries σ O} (he : e ∈ wtPart O wt w) (G : MvPowerSeries σ O) (j : X) :
    wcomp O wt j (G * e) = wcomp O wt (j - w) G * e := by
  classical
  ext n
  rw [coeff_wcomp, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = w
    · rw [coeff_wcomp, if_pos]
      rw [← h, ← hp', map_add (f := _), h2, add_sub_cancel_right]
    · rw [he _ h2, mul_zero, mul_zero]
  · symm
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = w
    · rw [coeff_wcomp, if_neg, zero_mul]
      intro h1
      apply h
      rw [← hp', map_add (f := _), h1, h2, sub_add_cancel]
    · rw [he _ h2, mul_zero]

private theorem lc_wcomp_self (O : Type) [CommRing O] {σ X : Type} [AddCommGroup X] (wt : σ → X)
    {w : X} {e : MvPowerSeries σ O} (he : e ∈ wtPart O wt w) : wcomp O wt w e = e := by
  ext n
  rw [coeff_wcomp]
  split_ifs with h
  · rfl
  · exact (he n h).symm

private theorem lc_inv {E τ ι : Type} [CommRing E] [Fintype ι] [DecidableEq ι] (w : τ → ℤ) (u : ι → ℤ)
    (A B : Matrix ι ι (MvPowerSeries τ E)) (h1 : A * B = 1) (h2 : B * A = 1)
    (hA : ∀ a b, A a b ∈ wtPart E w (u a - u b)) (a b : ι) : B a b ∈ wtPart E w (u a - u b) := by
  let B' : Matrix ι ι (MvPowerSeries τ E) := Matrix.of fun a b => wcomp E w (u a - u b) (B a b)
  have h3 : B' * A = 1 := by
    ext1 a c
    have e : (B' * A) a c = wcomp E w (u a - u c) ((B * A) a c) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [lc_wcomp_mul E w (hA b c)]
      have : u a - u c - (u b - u c) = u a - u b := by ring
      rw [this]; rfl
    rw [e, h2]
    by_cases hac : a = c
    · subst hac
      rw [Matrix.one_apply_eq, sub_self]
      exact lc_wcomp_self E w (one_mem_wtPart E w)
    · rw [Matrix.one_apply_ne hac, map_zero]
  have h4 : B' = B := by
    rw [← Matrix.mul_one B', ← h1, ← Matrix.mul_assoc, h3, Matrix.one_mul]
  rw [← h4]
  exact wcomp_mem E w _ _

private theorem lc_JMJ {R : Type} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    (Jmat R 3 * Mᵀ * Jmat R 3) a b = M b.rev a.rev := by
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

private theorem lc_emb {E τ : Type} [CommRing E] (w : τ → ℤ) (x : GG (m := 3) (R := MvPowerSeries τ E))
    (hx : ∀ a b, x.mat a b ∈ wtPart E w (wt a b)) (a b : Fin 3 ⊕ Fin 3) :
    emb x a b ∈ wtPart E w (wt6 a - wt6 b) := by
  have hθ : ∀ a b, (theta x.left : Matrix (Fin 3) (Fin 3) (MvPowerSeries τ E)) a b ∈ wtPart E w (wt1 a - wt1 b) := by
    intro a b
    rw [theta_val, lc_JMJ]
    have := lc_inv w wt1 x.mat ((x.left⁻¹ : GL (Fin 3) _) : Matrix (Fin 3) (Fin 3) (MvPowerSeries τ E))
      (Units.mul_inv x.left) (Units.inv_mul x.left) hx b.rev a.rev
    have e : ∀ a b : Fin 3, wt1 b.rev - wt1 a.rev = wt1 a - wt1 b := by decide
    rwa [e] at this
  rw [emb_apply]
  split_ifs <;> rcases a with a | a <;> rcases b with b | b <;>
    first
    | exact hx a b
    | exact hθ a b
    | exact zero_mem _

private theorem lc_order {K τ : Type} [CommRing K] (n : ℕ) :
    ∀ g ∈ RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries τ K →+* K) ^ n, (n : ℕ∞) ≤ g.order := by
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) ?_
    · refine le_trans ?_ MvPowerSeries.le_order_mul
      push_cast
      exact add_le_add (ih a ha) (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.2 hb)
    · intro a b ha hb
      exact le_trans (le_min ha hb) MvPowerSeries.min_order_le_add

private theorem lc_graded {O E σ τ : Type} [CommRing O] [CommRing E] [Algebra O E] [Finite σ] (v : σ → ℤ) (w : τ → ℤ)
    (Φ : MvPowerSeries σ O →ₐ[O] MvPowerSeries τ E)
    (h0 : ∀ s, MvPowerSeries.constantCoeff (Φ (MvPowerSeries.X s)) = 0)
    (h1 : ∀ s, Φ (MvPowerSeries.X s) ∈ wtPart E w (v s)) (j : ℤ) (F : MvPowerSeries σ O) (hF : F ∈ wtPart O v j) :
    Φ F ∈ wtPart E w j := by
  intro d hd
  obtain ⟨y, hy, hm⟩ := approx v Φ (RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries τ E →+* E))
    (fun j => (wtPart E w j).restrictScalars O) (one_mem_wtPart E w)
    (fun i j a ha b hb => mul_mem_wtPart E w ha hb) h0 h1 j F hF (d.degree + 1)
  have h2 : MvPowerSeries.coeff d (Φ F - y) = 0 := by
    refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (lc_order _ _ hm))
    exact_mod_cast Nat.lt_succ_self _
  rwa [map_sub, hy d hd, sub_zero] at h2

theorem UpperTheory.exists_origin_and_chart_of_isLocPres :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {H : Type} [Group H] [TopologicalSpace H] {η : H →* ℤˣ} {Ψ : H →* Oˣ}
          (U : Univ (GCond.noCondition O η Ψ)) (I : Ideal U.R) (x : U.R →ₐ[O] O) {τ : Type} [Fintype τ] (w : τ → ℤ) (φ : U.R →ₐ[O] MvPowerSeries τ (FractionRing O))
          (WB : WPres O ℤ (U.R ⧸ I)), IsBase η Ψ U.r.hom x → LocChart U I x w φ → IsLocPres U I WB →
          ∃ hB : WB.HasOrigin, (WB.origin hB).comp (Ideal.Quotient.mkₐ O I) = x ∧
            ∃ φb : (U.R ⧸ I) →ₐ[O] MvPowerSeries τ (FractionRing O), IsChart WB.part (WB.origin hB) w φb := by
  intro O _ _ _ H _ _ η Ψ U I x τ _ w φ WB hx hφ hW
  have hφI : ∀ f ∈ I, φ f = 0 := fun f hf => by rw [← hφ.ker] at hf; exact hf
  have hxI : ∀ f ∈ I, x f = 0 := fun f hf => by
    apply IsFractionRing.injective O (FractionRing O)
    rw [← hφ.const, hφI f hf, map_zero, map_zero]
  let xb : (U.R ⧸ I) →ₐ[O] O := Ideal.Quotient.liftₐ I x hxI
  let φb : (U.R ⧸ I) →ₐ[O] MvPowerSeries τ (FractionRing O) := Ideal.Quotient.liftₐ I φ hφI
  have hxb : ∀ f, xb (Ideal.Quotient.mkₐ O I f) = x f := fun f => rfl
  have hφb : ∀ f, φb (Ideal.Quotient.mkₐ O I f) = φ f := fun f => rfl
  have hz : ∀ s, ∃ g a b, WB.wt s = wt6 a - wt6 b ∧ WB.z s =
      Ideal.Quotient.mkₐ O I (emb (U.r.hom g) a b - algebraMap O U.R (emb (r0 η Ψ g) a b)) := fun s => by
    obtain ⟨g, a, b, h1, h2⟩ := hW.1 s
    exact ⟨g, a, b, h1, by rw [h2, emb_push, map_sub, AlgHom.commutes]⟩
  have hz0 : ∀ s, xb (WB.z s) = 0 := fun s => by
    obtain ⟨g, a, b, -, h2⟩ := hz s
    rw [h2, hxb]
    exact base_coord hx g a b
  have hconst : ∀ f, MvPowerSeries.constantCoeff (φb f) = algebraMap O (FractionRing O) (xb f) := fun f => by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective O I f
    rw [hφb, hxb, hφ.const]
  obtain ⟨hB, hO⟩ := origin_of WB xb hz0
  refine ⟨hB, by rw [hO]; exact AlgHom.ext hxb, φb, ?_⟩
  rw [hO]
  refine ⟨?_, hconst, fun i => ?_, fun f hf0 hf1 => ?_⟩
  · rintro j _ ⟨F, hF, rfl⟩
    refine lc_graded WB.wt w (φb.comp WB.π) (fun s => ?_) (fun s => ?_) j F hF
    · show MvPowerSeries.constantCoeff (φb (WB.z s)) = 0
      rw [hconst, hz0, map_zero]
    · show φb (WB.z s) ∈ _
      obtain ⟨g, a, b, h1, h2⟩ := hz s
      rw [h2, hφb, h1, map_sub, AlgHom.commutes, ← emb_push]
      refine sub_mem (lc_emb w _ (fun a b => hφ.graded g a b) a b) ?_
      by_cases hab : wt6 a = wt6 b
      · rw [hab, sub_self, Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_of_tower_mem _ _ (one_mem_wtPart _ w)
      · rw [unitaryEmbedding_residualRep_eq_zero_of_weight_ne η Ψ g a b hab, map_zero]
        exact zero_mem _
  · obtain ⟨f, hf⟩ := hφ.onto i
    exact ⟨Ideal.Quotient.mkₐ O I f, hf⟩
  · obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective O I f
    obtain ⟨c, hc, hf⟩ := hφ.inj f hf0 hf1
    refine ⟨c, hc, ?_⟩
    rw [← map_smul]
    have hle : RingHom.ker x ^ 2 ⊔ I ≤ (RingHom.ker xb ^ 2).comap (Ideal.Quotient.mkₐ O I) := by
      refine sup_le ?_ fun y hy => ?_
      · refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) 2) (Ideal.le_comap_pow _ 2)
        exact hy
      · rw [Ideal.mem_comap, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hy]
        exact zero_mem _
    exact hle hf
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsPointDerivationEmbEntryEqSmulMatEntry
section
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

private theorem theta_entry {R : Type} [CommRing R] (g : GL (Fin 3) R) (i j : Fin 3) :
    (theta g : Matrix (Fin 3) (Fin 3) R) i j = ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) j.rev i.rev := by
  rw [theta_val]
  simp [Matrix.mul_apply, Jmat]
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro k _ hk
    rw [if_neg]
    intro h
    apply hk
    rw [h, Fin.rev_rev]
  · simp

private theorem der_inv {O R Q : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup Q] [Module O Q]
    (x : R →ₐ[O] O) (D : R →ₗ[O] Q) (hD : D ∈ PtDer x Q) (t : Oˣ) (g : GL (Fin 3) R)
    (hg : GeneralLinearGroup.map (x : R →+* O) g = tor O t) (p q : Fin 3) :
    D (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) p q) =
      (-((((t ^ wt1 q)⁻¹ : Oˣ) : O) * (((t ^ wt1 p)⁻¹ : Oˣ) : O))) • D ((g : Matrix (Fin 3) (Fin 3) R) p q) := by
  have hDm : ∀ f h : R, D (f * h) = x f • D h + x h • D f := hD
  have hD1 : D 1 = 0 := by
    have h := hDm 1 1
    simp only [mul_one, map_one, one_smul] at h
    have h' : D 1 + D 1 = D 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h'
  have hx : ∀ i j, x ((g : Matrix (Fin 3) (Fin 3) R) i j) =
      ((tor O t : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) i j := by
    intro i j
    rw [← hg]
    rfl
  have hxi : ∀ i j, x (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) i j) =
      (((tor O t)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) i j := by
    intro i j
    rw [← hg, ← map_inv]
    rfl
  have htor : ((tor O t : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) =
      diagonal fun i => ((t ^ wt1 i : Oˣ) : O) := rfl
  have htori : (((tor O t)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) =
      diagonal fun i => (((t ^ wt1 i)⁻¹ : Oˣ) : O) := rfl
  have h1 : D ((1 : Matrix (Fin 3) (Fin 3) R) p q) = 0 := by
    rw [Matrix.one_apply]
    split_ifs
    · exact hD1
    · exact map_zero D
  have key := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => D (M p q))
    (congrArg (fun h : GL (Fin 3) R => (h : Matrix (Fin 3) (Fin 3) R)) (mul_inv_cancel g))
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Units.val_mul, Units.val_one, h1, Matrix.mul_apply, map_sum, hDm, hx, hxi, htor, htori,
    Finset.sum_add_distrib, diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at key
  have e : ((t ^ wt1 p : Oˣ) : O) • D (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) p q) =
      -((((t ^ wt1 q)⁻¹ : Oˣ) : O) • D ((g : Matrix (Fin 3) (Fin 3) R) p q)) :=
    eq_neg_of_add_eq_zero_left key
  calc D (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) p q)
      = (((t ^ wt1 p)⁻¹ : Oˣ) : O) • ((t ^ wt1 p : Oˣ) : O) •
          D (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) p q) := by
        rw [smul_smul, Units.inv_mul, one_smul]
    _ = _ := by
        rw [e, smul_neg, smul_smul, neg_smul, mul_comm (((t ^ wt1 q)⁻¹ : Oˣ) : O)]

private theorem map_left_eq_tor_and_right_eq_of_map_eq {O R : Type} [CommRing O] [CommRing R] [Algebra O R]
    (s : ℤˣ) (t : Oˣ) (x : R →ₐ[O] O) (y : GG (m := 3) (R := R))
    (hy : GG.map (x : R →+* O) y = ⟨tor O t, s⟩) :
    GeneralLinearGroup.map (x : R →+* O) y.left = tor O t ∧ y.right = s := by
  constructor
  · have h := congrArg SemidirectProduct.left hy
    simpa [GG.map] using h
  · have h := congrArg SemidirectProduct.right hy
    simpa [GG.map] using h

private theorem wt_rev_rev_eq_wt1_sub_wt1 (i j : Fin 3) : wt j.rev i.rev = wt1 i - wt1 j := by
  fin_cases i <;> fin_cases j <;> decide

theorem UpperTheory.exists_pointDerivation_emb_entry_eq_smul_mat_entry :
    ∀ {O : Type} [CommRing O] (s : ℤˣ) (t : Oˣ) (a b : Fin 3 ⊕ Fin 3), ∃ (u : O) (a' b' : Fin 3), wt a' b' = wt6 a - wt6 b ∧
          ∀ {R Q : Type} [CommRing R] [Algebra O R] [AddCommGroup Q] [Module O Q] (x : R →ₐ[O] O),
            ∀ D ∈ PtDer x Q, ∀ y : GG (m := 3) (R := R),
            GG.map (x : R →+* O) y = ⟨tor O t, s⟩ → D (emb y a b) = u • D (y.mat a' b') := by
  intro O _ s t a b
  by_cases hs : s = 1
  · rcases a with i | i <;> rcases b with j | j
    · refine ⟨1, i, j, by simp [wt6, wt], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨_, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_pos (hr.trans hs)]
      simp [GG.mat]
    · refine ⟨0, i, j, by simp [wt6, wt], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨_, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_pos (hr.trans hs)]
      simp
    · refine ⟨0, i, j, by simp [wt6, wt], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨_, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_pos (hr.trans hs)]
      simp
    · refine ⟨-((((t ^ wt1 i.rev)⁻¹ : Oˣ) : O) * (((t ^ wt1 j.rev)⁻¹ : Oˣ) : O)), j.rev, i.rev,
        by simp [wt6, wt_rev_rev_eq_wt1_sub_wt1], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨hl, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_pos (hr.trans hs)]
      simp only [fromBlocks_apply₂₂]
      rw [theta_entry]
      exact der_inv x D hD t y.left hl j.rev i.rev
  · rcases a with i | i <;> rcases b with j | j
    · refine ⟨0, i, j, by simp [wt6, wt], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨_, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_neg (by rw [hr]; exact hs)]
      simp
    · refine ⟨1, i, j, by simp [wt6, wt], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨_, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_neg (by rw [hr]; exact hs)]
      simp [GG.mat]
    · refine ⟨-((((t ^ wt1 i.rev)⁻¹ : Oˣ) : O) * (((t ^ wt1 j.rev)⁻¹ : Oˣ) : O)), j.rev, i.rev,
        by simp [wt6, wt_rev_rev_eq_wt1_sub_wt1], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨hl, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_neg (by rw [hr]; exact hs)]
      simp only [fromBlocks_apply₂₁]
      rw [theta_entry]
      exact der_inv x D hD t y.left hl j.rev i.rev
    · refine ⟨0, i, j, by simp [wt6, wt], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨_, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_neg (by rw [hr]; exact hs)]
      simp
end

