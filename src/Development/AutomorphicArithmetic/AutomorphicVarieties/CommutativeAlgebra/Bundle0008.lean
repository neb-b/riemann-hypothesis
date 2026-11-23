module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0048

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KrullDimQuotientComapEq
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem krull_dim_quotient_comap_eq {k Z A B C : Type} [Field k] [AddCommGroup Z] [Module k Z] [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C] [Module.Finite k A] [Module.Finite k C]
    (δ : Z →ₗ[k] A) (β : A →ₗ[k] B) (p : B →ₗ[k] C) (h0 : Function.Injective δ)
    (h1 : LinearMap.range δ = LinearMap.ker β) (h2 : LinearMap.range β = LinearMap.ker p) :
    Module.finrank k Z + Module.finrank k B = Module.finrank k A + Module.finrank k (LinearMap.range p) := by
  have hB : Module.Finite k B := by
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker p (IsNoetherian.noetherian _) ?_⟩
    rw [top_inf_eq, ← h2, LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top
  have e1 := LinearMap.finrank_range_add_finrank_ker β
  have e2 := LinearMap.finrank_range_add_finrank_ker p
  have e3 := LinearMap.finrank_range_of_inj h0
  rw [← h1, h2] at e1
  omega

private theorem cob_lc {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup M] [Module k M] (ρ : Representation k Γ M) (h : IsOpen (ρ.ker : Set Γ)) (m : M) :
    IsLocallyConstant (fun g => ρ g m - m) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (ρ.ker : Set Γ), h.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  have hy' : ρ (x⁻¹ * y) = 1 := hy
  have : ρ y = ρ x := by
    conv_lhs => rw [← mul_inv_cancel_left x y, map_mul, hy', mul_one]
  rw [this]

theorem UpperTheory.V.Alg.finrank_compact_support_H1 :
    ∀ (k Γ M : Type) [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M]
      (ρ : Representation k Γ M), IsOpen (ρ.ker : Set Γ) → ∀ (F : Frame Γ), (∀ q, ∀ n ∈ F.N q, ρ (F.ψ q n) = 1) → Module.Finite k (ReciprocityTheory.Gal.H1 ρ) →
      Module.finrank k (ReciprocityTheory.Gal.H0 ρ) + Module.finrank k (F.H1c ρ) = ∑ v, Module.finrank k (ReciprocityTheory.Gal.H0 (ρ.comp (F.φ v) : Representation k _ M)) +
        Module.finrank k (ReciprocityTheory.Gal.Sha1 ρ F.φ F.hφ ⊓ ReciprocityTheory.Gal.Sel ρ F.ψ F.hψ (fun q => ReciprocityTheory.Gal.H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)) : Submodule k (ReciprocityTheory.Gal.H1 ρ)) := by
  intro k Γ M _ _ _ _ _ _ _ _ _ _ _ ρ hρ F hN hfin
  classical
  let δ : ReciprocityTheory.Gal.H0 ρ →ₗ[k] (∀ v, ReciprocityTheory.Gal.H0 (ρ.comp (F.φ v) : Representation k _ M)) :=
    LinearMap.pi fun v => ReciprocityTheory.Gal.resH0 ρ (F.φ v)
  let β : (∀ v, ReciprocityTheory.Gal.H0 (ρ.comp (F.φ v) : Representation k _ M)) →ₗ[k] F.H1c ρ :=
    { toFun := fun b => ⟨(fun g => ρ g (-(b F.v0).1) - (-(b F.v0).1), fun v => (b v).1 - (b F.v0).1),
        cob_lc ρ hρ _, fun s t => by
          simp only [map_mul, Module.End.mul_apply, map_sub]; abel,
        fun q n hn => by simp [hN q n hn],
        fun v s => by
          have : ρ (F.φ v s) (b v).1 = (b v).1 := (b v).2 s
          simp only [map_sub, map_neg, this]; abel,
        sub_self _⟩
      map_add' := fun b b' => by
        apply Subtype.ext
        refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
        · simp; abel
        · simp; abel
      map_smul' := fun c b => by
        apply Subtype.ext
        refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
        · simp [smul_add]
        · simp [smul_sub] }
  let p0 : F.H1c ρ →ₗ[k] ReciprocityTheory.Gal.Z1 ρ :=
    { toFun := fun x => ⟨x.1.1, x.2.1.continuous, x.2.2.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let p : F.H1c ρ →ₗ[k] ReciprocityTheory.Gal.H1 ρ := (Submodule.mkQ _).comp p0
  have h0 : Function.Injective δ := by
    intro x y hxy
    have := congrArg (fun b => (b F.v0).1) hxy
    exact Subtype.ext this
  have h1 : LinearMap.range δ = LinearMap.ker β := by
    ext b
    rw [LinearMap.mem_ker]
    constructor
    · rintro ⟨m, rfl⟩
      apply Subtype.ext
      refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
      · change ρ g (-m.1) - (-m.1) = 0
        rw [map_neg, (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere ρ m.1).1 m.2 g, sub_self]
      · exact sub_self m.1
    · intro hb
      have e1 : ∀ g, ρ g (-(b F.v0).1) - (-(b F.v0).1) = 0 := fun g =>
        congrArg (fun x : F.H1c ρ => x.1.1 g) hb
      have e2 : ∀ v, (b v).1 - (b F.v0).1 = 0 := fun v =>
        congrArg (fun x : F.H1c ρ => x.1.2 v) hb
      refine ⟨⟨(b F.v0).1, (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere ρ _).2 fun g => ?_⟩, funext fun v => Subtype.ext ?_⟩
      · have := e1 g
        rw [map_neg, sub_eq_zero] at this
        exact neg_injective this
      · exact (sub_eq_zero.1 (e2 v)).symm
  have h2 : LinearMap.range β = LinearMap.ker p := by
    ext x
    rw [LinearMap.mem_ker]
    change _ ↔ Submodule.Quotient.mk (p0 x) = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨-(b F.v0).1, fun g => rfl⟩
    · rintro ⟨m, hm⟩
      have hm' : ∀ g, x.1.1 g = ρ g m - m := hm
      obtain ⟨-, -, -, a4, a5⟩ := x.2
      refine ⟨fun v => ⟨x.1.2 v - m, (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun s => ?_⟩, ?_⟩
      · change ρ (F.φ v s) (x.1.2 v - m) = x.1.2 v - m
        have := a4 v s
        rw [hm'] at this
        rw [map_sub, sub_eq_sub_iff_sub_eq_sub, this]
      · apply Subtype.ext
        refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
        · change ρ g (-(x.1.2 F.v0 - m)) - (-(x.1.2 F.v0 - m)) = x.1.1 g
          rw [a5, hm']; simp
        · change x.1.2 v - m - (x.1.2 F.v0 - m) = x.1.2 v
          rw [a5]; abel
  have key : ∀ c : ReciprocityTheory.Gal.Z1 ρ, (Submodule.Quotient.mk c : ReciprocityTheory.Gal.H1 ρ) ∈
      (ReciprocityTheory.Gal.Sha1 ρ F.φ F.hφ ⊓ ReciprocityTheory.Gal.Sel ρ F.ψ F.hψ (fun q => ReciprocityTheory.Gal.H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)) : Submodule k (ReciprocityTheory.Gal.H1 ρ)) ↔
      (∀ v, ∃ m, ∀ s, c.1 (F.φ v s) = ρ (F.φ v s) m - m) ∧ ∀ q, ∀ n ∈ F.N q, c.1 (F.ψ q n) = 0 := by
    intro c
    rw [Submodule.mem_inf, ReciprocityTheory.Gal.mem_Sel, ReciprocityTheory.Gal.Sha1, Submodule.mem_iInf]
    refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun q => ?_)
    · rw [LinearMap.mem_ker, ReciprocityTheory.Gal.resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
      rfl
    · rw [ReciprocityTheory.Gal.H1ur, LinearMap.mem_ker, ReciprocityTheory.Gal.resH1]
      refine (Submodule.Quotient.mk_eq_zero _).trans ?_
      rw [ Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
      constructor
      · rintro ⟨m, hm⟩ n hn
        have : c.1 (F.ψ q n) = ρ (F.ψ q n) m - m := hm ⟨n, hn⟩
        rw [this, hN q n hn]; simp
      · intro h
        refine ⟨0, fun n => ?_⟩
        change c.1 (F.ψ q n.1) = ρ (F.ψ q n.1) 0 - 0
        rw [h n.1 n.2]; simp
  have h3 : LinearMap.range p = (ReciprocityTheory.Gal.Sha1 ρ F.φ F.hφ ⊓ ReciprocityTheory.Gal.Sel ρ F.ψ F.hψ (fun q => ReciprocityTheory.Gal.H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)) : Submodule k (ReciprocityTheory.Gal.H1 ρ)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨-, -, a3, a4, -⟩ := x.2
      exact (key (p0 x)).2 ⟨fun v => ⟨x.1.2 v, a4 v⟩, a3⟩
    · intro hy
      obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨k1, k2⟩ := (key c).1 hy
      choose m hm using k1
      refine ⟨⟨(fun g => c.1 g - (ρ g (m F.v0) - m F.v0), fun v => m v - m F.v0),
        ((IsLocallyConstant.iff_continuous _).2 c.2.1).sub (cob_lc ρ hρ _), fun s t => ?_, fun q n hn => ?_,
        fun v s => ?_, sub_self _⟩, ?_⟩
      · simp only [c.2.2 s t, map_mul, Module.End.mul_apply, map_sub]; abel
      · simp [k2 q n hn, hN q n hn]
      · simp only [hm, map_sub]; abel
      · change Submodule.Quotient.mk _ = _
        rw [Submodule.Quotient.eq, Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
        refine ⟨-m F.v0, fun g => ?_⟩
        change c.1 g - (ρ g (m F.v0) - m F.v0) - c.1 g = _
        rw [map_neg]; abel
  have := krull_dim_quotient_comap_eq δ β p h0 h1 h2
  rw [h3, Module.finrank_pi_fintype] at this
  exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartFilt
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem UpperTheory.V.Alg.part_filt_coeff {O σ : Type} [CommRing O] [IsLocalRing O] (M : ℕ) :
    ∀ f ∈ maximalIdeal (MvPowerSeries σ O) ^ M, ∀ n : σ →₀ ℕ,
      coeff n f ∈ maximalIdeal O ^ (M - n.degree) :=
  _root_.UpperTheory.Reformulated.B.PartialFiltrationCoeff.part_filt_coeff M

private theorem UpperTheory.V.Alg.part_filt_split {σ X : Type} [Finite σ] [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (wt : σ → X) (j : X) :
    ∃ D : ℕ, ∀ n : σ →₀ ℕ, Finsupp.weight wt n = j → D < n.degree →
      ∃ g n' : σ →₀ ℕ, g ≠ 0 ∧ Finsupp.weight wt g = 0 ∧ g.degree ≤ D ∧ n = g + n' := by
  classical
  obtain ⟨g, hg, hcl, hj⟩ := UpperTheory.V.Alg.gordan σ X wt
  obtain ⟨μ, hμ, hμ'⟩ := hj j
  refine ⟨(g ∪ μ).sup Finsupp.degree, fun n hn hD => ?_⟩
  obtain ⟨m, hm, hmn⟩ := hμ' n hn
  obtain ⟨r, rfl⟩ := exists_add_of_le hmn
  have hr : Finsupp.weight wt r = 0 := by
    rw [map_add (f := _), hμ m hm] at hn
    simpa using hn
  have hr0 : r ≠ 0 := by
    rintro rfl
    have : m.degree ≤ (g ∪ μ).sup Finsupp.degree :=
      Finset.le_sup (f := Finsupp.degree) (Finset.mem_union_right _ hm)
    rw [add_zero] at hD
    omega
  have key : ∀ r ∈ AddSubmonoid.closure (g : Set (σ →₀ ℕ)), r = 0 ∨ ∃ a ∈ g, a ≤ r := by
    intro r hr
    induction hr using AddSubmonoid.closure_induction with
    | mem x hx => exact Or.inr ⟨x, hx, le_rfl⟩
    | zero => exact Or.inl rfl
    | add x y _ _ hx hy =>
      rcases hx with rfl | ⟨a, ha, hax⟩
      · simpa using hy
      · exact Or.inr ⟨a, ha, hax.trans le_self_add⟩
  obtain ⟨a, ha, har⟩ := (key r (hcl r hr)).resolve_left hr0
  obtain ⟨b, rfl⟩ := exists_add_of_le har
  exact ⟨a, m + b, (hg a ha).1, (hg a ha).2,
    Finset.le_sup (f := Finsupp.degree) (Finset.mem_union_left _ ha), by abel⟩

private theorem UpperTheory.V.Alg.part_filt_monomial {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X)
    {j : X} {n : σ →₀ ℕ} (hn : Finsupp.weight wt n = j) (c : O) : monomial n c ∈ wtPart O wt j := by
  classical
  intro m hm
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact hm hn

theorem UpperTheory.V.Alg.part_filt :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (j : X) (n : ℕ), ∃ M : ℕ, W.part j ⊓ (maximalIdeal R ^ M).restrictScalars O ≤ (W.part 0 ⊓ (maximalIdeal R).restrictScalars O) ^ n * W.part 0 * W.part j := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W _ j k
  classical
  set Q : Submodule O R := W.part 0 ⊓ (maximalIdeal R).restrictScalars O with hQ
  have hloc : IsLocalHom (W.π : MvPowerSeries W.σ O →+* R) := IsLocalHom.of_surjective _ W.surj
  have hone : (1 : R) ∈ W.part 0 := ⟨1, one_mem_wtPart O W.wt, map_one W.π⟩

  have hmono : ∀ k : ℕ, ∃ N : ℕ, ∀ n : W.σ →₀ ℕ, Finsupp.weight W.wt n = j → N ≤ n.degree →
      W.π (monomial n 1) ∈ Q ^ k * W.part j := by
    obtain ⟨D, hD⟩ := UpperTheory.V.Alg.part_filt_split W.wt j
    intro k
    induction k with
    | zero =>
      refine ⟨0, fun n hn _ => ?_⟩
      rw [pow_zero, one_mul]
      exact ⟨_, UpperTheory.V.Alg.part_filt_monomial W.wt hn 1, rfl⟩
    | succ k ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨N + D + 1, fun n hn hd => ?_⟩
      obtain ⟨g, n', hg0, hgw, hgd, rfl⟩ := hD n hn (by omega)
      rw [map_add (f := _)] at hd
      rw [map_add (f := _), hgw, zero_add] at hn
      have h1 := hN n' hn (by omega)
      have h2 : W.π (monomial g 1) ∈ Q := by
        refine ⟨⟨_, UpperTheory.V.Alg.part_filt_monomial W.wt hgw 1, rfl⟩, ?_⟩
        intro hu
        have h3 : IsUnit (monomial g (1 : O)) := hloc.map_nonunit _ hu
        rw [MvPowerSeries.isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, coeff_monomial,
          if_neg hg0.symm] at h3
        exact not_isUnit_zero h3
      have h4 : (monomial (g + n') (1 : O) : MvPowerSeries W.σ O) = monomial g 1 * monomial n' 1 := by
        rw [monomial_mul_monomial, one_mul]
      rw [h4, map_mul, pow_succ', mul_assoc]
      exact Submodule.mul_mem_mul h2 h1

  have hconst : ∀ k : ℕ, ∀ c ∈ maximalIdeal O ^ k, algebraMap O R c ∈ Q ^ k := by
    intro k
    induction k with
    | zero =>
      intro c _
      rw [pow_zero]
      exact Submodule.algebraMap_mem c
    | succ k ih =>
      intro c hc
      rw [pow_succ] at hc
      refine Submodule.mul_induction_on hc (fun a ha b hb => ?_) (fun a b ha hb => ?_)
      · rw [map_mul, pow_succ]
        refine Submodule.mul_mem_mul (ih a ha) ⟨?_, ?_⟩
        · rw [Algebra.algebraMap_eq_smul_one]
          exact Submodule.smul_mem _ _ hone
        · exact fun hu => hb (IsLocalHom.map_nonunit (f := algebraMap O R) b hu)
      · rw [map_add (f := _)]
        exact add_mem ha hb
  obtain ⟨N, hN⟩ := hmono k
  refine ⟨N + k, ?_⟩
  rintro x ⟨⟨f, hf, hfx⟩, hx⟩
  have hfx' : W.π f = x := hfx
  have hle : maximalIdeal R ≤ (maximalIdeal (MvPowerSeries W.σ O)).map W.π := by
    intro y hy
    obtain ⟨g, rfl⟩ := W.surj y
    exact Ideal.mem_map_of_mem _ fun hu => hy (hu.map W.π)
  have hx' : x ∈ (maximalIdeal (MvPowerSeries W.σ O) ^ (N + k)).map W.π := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hle _ hx
  obtain ⟨g, hg, hgx⟩ := (Ideal.mem_map_iff_of_surjective W.π W.surj).1 hx'
  set h := wcomp O W.wt j g with hh
  have hhx : W.π h = x := by
    have h1 : f - g ∈ RingHom.ker W.π := by
      rw [RingHom.mem_ker, map_sub, hfx', hgx, sub_self]
    have h2 := W.homog _ h1 j
    have h3 : wcomp O W.wt j f = f := by
      ext n
      rw [coeff_wcomp]
      split_ifs with hn
      · rfl
      · exact (hf n hn).symm
    rw [map_sub, h3, RingHom.mem_ker, map_sub, hfx', sub_eq_zero] at h2
    exact h2.symm
  have hhj : h ∈ wtPart O W.wt j := wcomp_mem O W.wt j g
  have hhc : ∀ n : W.σ →₀ ℕ, n.degree < N → coeff n h ∈ maximalIdeal O ^ k := by
    intro n hn
    rw [hh, coeff_wcomp]
    split_ifs
    · exact Ideal.pow_le_pow_right (by omega) (UpperTheory.V.Alg.part_filt_coeff _ g hg n)
    · exact zero_mem _
  have hfin : {n : W.σ →₀ ℕ | n.degree < N}.Finite :=
    (Finsupp.finite_of_degree_le N).subset fun n (hn : n.degree < N) => hn.le
  set low : MvPowerSeries W.σ O := ∑ n ∈ hfin.toFinset, monomial n (coeff n h) with hlow
  have hlowc : ∀ m, coeff m low = if m.degree < N then coeff m h else 0 := by
    intro m
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hlow, map_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq]
    simp
  obtain ⟨μ, hμ, hspan⟩ := UpperTheory.V.Alg.part_span O R X W
    {n | Finsupp.weight W.wt n = j ∧ N ≤ n.degree} j fun n hn => hn.1
  obtain ⟨b, hb, hhigh⟩ := hspan (h - low) (by
    intro n hn
    rw [map_sub, hlowc]
    split_ifs with hd
    · exact sub_self _
    · rw [sub_zero]
      exact hhj n fun hw => hn ⟨hw, not_lt.1 hd⟩)
  have hsum : x = W.π low + W.π (h - low) := by rw [← map_add (f := _), add_sub_cancel, hhx]
  rw [hsum]
  refine add_mem ?_ ?_
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [hlow, map_sum]
    refine Submodule.sum_mem _ fun n hn => ?_
    by_cases hw : Finsupp.weight W.wt n = j
    · have h1 : W.π (monomial n (coeff n h)) = algebraMap O R (coeff n h) * 1 * W.π (monomial n 1) := by
        rw [mul_one, ← Algebra.smul_def, ← map_smul, ← map_smul, smul_eq_mul, mul_one]
      rw [h1]
      exact Submodule.mul_mem_mul
        (Submodule.mul_mem_mul (hconst k _ (hhc n (hfin.mem_toFinset.1 hn))) hone)
        ⟨_, UpperTheory.V.Alg.part_filt_monomial W.wt hw 1, rfl⟩
    · rw [hhj n hw, map_zero, map_zero]
      exact zero_mem _
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [hhigh, map_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    rw [map_mul, mul_comm (Q ^ k), mul_assoc]
    exact Submodule.mul_mem_mul ⟨_, hb m, rfl⟩ (hN m (hμ hm).1 (hμ hm).2)
end

