module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0062

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ExistsLimitOfSuccessiveDiffMemFiltration
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.exists_limit_of_successive_diff_mem_filtration :
    ∀ (P : Type) [CommRing P] (m : Ideal P) [IsPrecomplete m P] (J : ℕ → Ideal P), (∀ N, m ^ (N + 1) ≤ J N) → (∀ N, J N ≤ J (N + 1) ⊔ m ^ (N + 1)) → ∀ (N₀ : ℕ) (p : ℕ → P), (∀ N, N₀ ≤ N → p (N + 1) - p N ∈ J N) → ∃ x : P, (∀ N, N₀ ≤ N → x - p N ∈ J N) ∧ x - p N₀ ∈ m ^ (N₀ + 1) := by
  intro P _ m _ J hmJ hJ N₀ p hp
  classical
  have hsm : ∀ n, (m ^ n • ⊤ : Submodule P P) = m ^ n := by
    intro n
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have step : ∀ (k : ℕ) (y : P), ∃ y' : P,
      y - p (N₀ + k) ∈ J (N₀ + k) →
        y' - p (N₀ + k + 1) ∈ J (N₀ + k + 1) ∧ y' - y ∈ m ^ (N₀ + k + 1) := by
    intro k y
    by_cases hy : y - p (N₀ + k) ∈ J (N₀ + k)
    · have h1 : y - p (N₀ + k + 1) ∈ J (N₀ + k) := by
        have h := sub_mem hy (hp (N₀ + k) (Nat.le_add_right _ _))
        have e : y - p (N₀ + k + 1) = y - p (N₀ + k) - (p (N₀ + k + 1) - p (N₀ + k)) := by ring
        rw [e]
        exact h
      obtain ⟨j, hj, t, ht, hjt⟩ := Submodule.mem_sup.1 (hJ (N₀ + k) h1)
      refine ⟨y - t, fun _ => ⟨?_, ?_⟩⟩
      · have e : y - t - p (N₀ + k + 1) = j := by
          rw [sub_right_comm, ← hjt]
          ring
        rw [e]
        exact hj
      · rw [sub_sub_cancel_left]
        exact neg_mem ht
    · exact ⟨y, fun h => absurd h hy⟩
  choose g hg using step
  let q : ℕ → P := fun k => Nat.rec (p N₀) (fun k y => g k y) k
  have hq0 : q 0 = p N₀ := rfl
  have hqs : ∀ k, q (k + 1) = g k (q k) := fun k => rfl
  have hqJ : ∀ k, q k - p (N₀ + k) ∈ J (N₀ + k) ∧ q (k + 1) - q k ∈ m ^ (N₀ + k + 1) := by
    intro k
    induction k with
    | zero =>
      have h0 : q 0 - p (N₀ + 0) ∈ J (N₀ + 0) := by simp [hq0]
      exact ⟨h0, by rw [hqs]; exact (hg 0 (q 0) h0).2⟩
    | succ k ih =>
      have h0 : q (k + 1) - p (N₀ + (k + 1)) ∈ J (N₀ + (k + 1)) := by
        rw [hqs]
        exact (hg k (q k) ih.1).1
      exact ⟨h0, by rw [hqs (k + 1)]; exact (hg (k + 1) (q (k + 1)) h0).2⟩
  have hcau : ∀ a b, a ≤ b → q b - q a ∈ m ^ (N₀ + a + 1) := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      have h := add_mem (Ideal.pow_le_pow_right (by omega) (hqJ b).2) ih
      rwa [sub_add_sub_cancel] at h
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := m) q (fun {a b} hab => by
    rw [hsm, SModEq.sub_mem, ← neg_sub]
    exact neg_mem (Ideal.pow_le_pow_right (by omega) (hcau a b hab)))
  have hx : ∀ k, L - q k ∈ m ^ (N₀ + k + 1) := by
    intro k
    have h1 := hL (N₀ + k + 1)
    rw [hsm, SModEq.sub_mem] at h1
    have h2 := hcau k (N₀ + k + 1) (by omega)
    have e : L - q k = -(q (N₀ + k + 1) - L) + (q (N₀ + k + 1) - q k) := by ring
    rw [e]
    exact add_mem (neg_mem h1) h2
  refine ⟨L, fun N hN => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    have e : L - p (N₀ + k) = (L - q k) + (q k - p (N₀ + k)) := by ring
    rw [e]
    exact add_mem (hmJ (N₀ + k) (hx k)) (hqJ k).1
  · simpa [hq0] using hx 0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FiniteLiftDualNumberOfPhiCond
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem pullback_fin_relation (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l] (Γ ι : Type) [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι k) [IsTopologicalGroup Γ]
    [CompactSpace Γ] (hΦ : PhiCond (Γ := Γ) l) (hlc : IsLocallyConstant rbar) :
    Finite {r : Γ →* Matrix ι ι (DualNumber k) //
      (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b} := by
  classical
  letI : Algebra (ZMod l) k := ZMod.algebra k l
  have hHopen : IsOpen (rbar.ker : Set Γ) := by
    have h := hlc.isOpen_fiber 1
    convert h using 1
    ext x
    simp [MonoidHom.mem_ker]
  haveI : Finite (Γ ⧸ rbar.ker) := Subgroup.quotient_finite_of_isOpen _ hHopen
  haveI := hΦ rbar.ker hHopen
  haveI : Finite (Module.Dual (ZMod l) k) :=
    Finite.of_injective (fun f => (f : k → ZMod l)) DFunLike.coe_injective
  haveI : Finite (DualNumber k) := inferInstanceAs (Finite (k × k))
  have hfst : ∀ r : {r : Γ →* Matrix ι ι (DualNumber k) //
      (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b},
      ∀ x ∈ rbar.ker, ∀ a b, (r.1 x a b).fst = (1 : Matrix ι ι k) a b := by
    intro r x hx a b
    rw [r.2.1, (MonoidHom.mem_ker).1 hx]
  have key : ∀ r : {r : Γ →* Matrix ι ι (DualNumber k) //
      (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b},
      ∀ x ∈ rbar.ker, ∀ y ∈ rbar.ker, ∀ a b,
        (r.1 (x * y) a b).snd = (r.1 x a b).snd + (r.1 y a b).snd := by
    intro r x hx y hy a b
    rw [map_mul, Matrix.mul_apply, TrivSqZeroExt.snd_sum]
    simp only [TrivSqZeroExt.snd_mul, hfst r x hx, hfst r y hy]
    simp [Finset.sum_add_distrib, Matrix.one_apply, ite_smul, add_comm]
  have hone : ∀ r : {r : Γ →* Matrix ι ι (DualNumber k) //
      (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b},
      ∀ a b, (r.1 1 a b).snd = 0 := by
    intro r a b
    rw [map_one]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  let φ : {r : Γ →* Matrix ι ι (DualNumber k) //
      (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b} →
      ι → ι → Module.Dual (ZMod l) k → (rbar.ker →* Multiplicative (ZMod l)) := fun r a b f =>
    { toFun := fun x => Multiplicative.ofAdd (f (r.1 x a b).snd)
      map_one' := by
        show Multiplicative.ofAdd (f (r.1 1 a b).snd) = 1
        rw [hone r a b, map_zero]
        rfl
      map_mul' := by
        intro x y
        simp only [Subgroup.coe_mul, key r x x.2 y y.2, map_add (f := _), ofAdd_add] }
  have hφopen : ∀ r a b f, IsOpen ((φ r a b f).ker : Set rbar.ker) := by
    intro r a b f
    have hlc' : IsLocallyConstant fun x : rbar.ker => φ r a b f x :=
      ((r.2.2 a b).comp_continuous continuous_subtype_val).comp
        (fun z => Multiplicative.ofAdd (f z.snd))
    have h := hlc'.isOpen_fiber 1
    convert h using 1
    ext x
    simp [MonoidHom.mem_ker]
  let F : {r : Γ →* Matrix ι ι (DualNumber k) //
      (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b} →
      (Γ ⧸ rbar.ker → Matrix ι ι (DualNumber k)) ×
        (ι → ι → Module.Dual (ZMod l) k →
          {φ : rbar.ker →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set rbar.ker)}) :=
    fun r => (fun q => r.1 q.out, fun a b f => ⟨φ r a b f, hφopen r a b f⟩)
  refine Finite.of_injective F ?_
  intro r s hrs
  have h1 : ∀ q : Γ ⧸ rbar.ker, r.1 q.out = s.1 q.out := fun q => congrFun (congrArg Prod.fst hrs) q
  have h2 : ∀ (a b : ι) (f : Module.Dual (ZMod l) k) (x : rbar.ker), f (r.1 x a b).snd = f (s.1 x a b).snd := by
    intro a b f x
    have h := congrArg (fun p => ((p.2 a b f).1 x)) hrs
    exact Multiplicative.ofAdd.injective h
  have hK : ∀ x ∈ rbar.ker, r.1 x = s.1 x := by
    intro x hx
    refine Matrix.ext fun a b => TrivSqZeroExt.ext ?_ ?_
    · rw [hfst r x hx, hfst s x hx]
    · have h := (Module.forall_dual_apply_eq_zero_iff (ZMod l) ((r.1 x a b).snd - (s.1 x a b).snd)).1
        (fun f => by rw [map_sub, h2 a b f ⟨x, hx⟩, sub_self])
      exact sub_eq_zero.1 h
  apply Subtype.ext
  ext1 g
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul rbar.ker g
  have hg : g = (QuotientGroup.mk g : Γ ⧸ rbar.ker).out * (h : Γ)⁻¹ := by
    rw [hh]
    group
  rw [hg, map_mul, map_mul, h1, hK _ (rbar.ker.inv_mem h.2)]

theorem UpperTheory.finite_lift_dualNumber_of_phiCond :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (Γ ι : Type) [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) [IsTopologicalGroup Γ] [CompactSpace Γ] [IsCO O (DualNumber (ResidueField O))], PhiCond (Γ := Γ) l → IsLocallyConstant rbar → Finite (Lift O rbar (DualNumber (ResidueField O))) := by
  intro l _ O _ _ _ _ Γ ι _ _ _ _ rbar _ _ _ hΦ hlc
  classical
  have hmem : ∀ x : DualNumber (ResidueField O), x ∈ maximalIdeal (DualNumber (ResidueField O)) ↔ x.fst = 0 := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero,
      not_not]
  have hres : ∀ x : DualNumber (ResidueField O), res O (DualNumber (ResidueField O)) x = x.fst := by
    intro x
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective x.fst
    have hx : x = algebraMap O (DualNumber (ResidueField O)) a + TrivSqZeroExt.inr x.snd := by
      rw [TrivSqZeroExt.algebraMap_eq_inl']
      refine TrivSqZeroExt.ext ?_ ?_
      · simp [IsLocalRing.ResidueField.algebraMap_eq, ha]
      · simp
    have hz : res O (DualNumber (ResidueField O)) (TrivSqZeroExt.inr x.snd) = 0 := by
      rw [res_eq_zero_iff, hmem]
      simp
    conv_lhs => rw [hx]
    rw [map_add (f := _), hz, add_zero, AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq, ha]
  have hsq : maximalIdeal (DualNumber (ResidueField O)) ^ 2 = ⊥ := by
    rw [sq, eq_bot_iff]
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    rw [hmem] at hx hy
    rw [Ideal.mem_bot]
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [hx]
    · simp [TrivSqZeroExt.snd_mul, hx, hy]
  have hinj : Function.Injective (Ideal.Quotient.mk (maximalIdeal (DualNumber (ResidueField O)) ^ 2)) := by
    intro x y hxy
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, hsq, Ideal.mem_bot, sub_eq_zero] at hxy
    exact hxy
  haveI := pullback_fin_relation l (ResidueField O) Γ ι rbar hΦ hlc
  refine Finite.of_injective
    (fun r : Lift O rbar (DualNumber (ResidueField O)) =>
      (⟨r.hom, fun g a b => by rw [← hres]; exact r.red g a b,
        fun a b => IsLocallyConstant.desc _ _ (r.cont a b 2) hinj⟩ :
        {r : Γ →* Matrix ι ι (DualNumber (ResidueField O)) //
          (∀ g a b, (r g a b).fst = rbar g a b) ∧ ∀ a b, IsLocallyConstant fun g => r g a b}))
    ?_
  intro r s hrs
  exact Lift.ext (congrArg Subtype.val hrs)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedOrigin
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.framed_origin :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q))), (∀ q, ∀ n ∈ F.N q, rbar (F.ψ q n) = 1) → (∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) → (∀ q, L q O (r0.comap (F.ψ q) (F.hψ q))) →
      ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B), (∀ v, Φ.InH (r0.hom.comp (F.φ v)) B (ρ v)) → ∀ (WB : WPres O X B) (hB : WB.HasOrigin), (∀ v s a b, WB.origin hB ((ρ v).hom s a b) = r0.hom (F.φ v s) a b) →
      ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (i : B →ₐ[O] R) (r : Lift O rbar R) (α : F.T → Matrix ι ι R), IsUnivFramed Φ r0.hom F L ρ i r α → ∀ (W : WPres O X R) (τ : Type) (e : WB.σ ⊕ τ ≃ W.σ), (∀ s, W.z (e (.inl s)) = i (WB.z s)) →
      (∀ t, ∃ a b, (∃ s, W.z (e (.inr t)) = r.hom s a b - algebraMap O R (r0.hom s a b)) ∨ ∃ v, W.z (e (.inr t)) = (α v - 1) a b) →
      ∃ h : W.HasOrigin, r.map (W.origin h) = r0 ∧ (∀ v, (α v).map (W.origin h) = 1) ∧ (W.origin h).comp i = WB.origin hB := by
  intro O _ _ _ _ ι X _ _ _ w Φ h2 Γ _ _ _ rbar r0 hbar hr0 F L hN hLoc hL0 B _ _ _ ρ hρ WB hB hWB R _ _ _ i r α hU W τ e hWl hWr
  have hHH1 : ∀ (S : Type) [CommRing S] [Algebra O S] [IsCO O S], Φ.HH (1 : Matrix ι ι S) := by
    intro S _ _ _
    refine ⟨by simp, fun a b hab => ?_, ?_⟩
    · exact Matrix.one_apply_ne (fun h => hab (h ▸ rfl))
    · simp
  have hF : IsFramed Φ r0.hom F L ρ (WB.origin hB) r0 (fun _ => (1 : Matrix ι ι O)) := by
    refine ⟨fun s => ?_, fun q => hL0 q, fun v => hHH1 O, rfl, fun v s => ?_⟩
    · have hm : (r0.hom s⁻¹).map (algebraMap O O) = r0.hom s⁻¹ := by
        ext a b
        simp
      rw [hm, ← map_mul, mul_inv_cancel, map_one]
      exact hHH1 O
    · ext a b
      simp [Matrix.map_apply, hWB]
  obtain ⟨f, ⟨hfi, hfr, hfα⟩, -⟩ := hU.2 O (WB.origin hB) r0 (fun _ => 1) hF
  have hz : ∀ s, f (W.z s) = 0 := by
    intro s
    obtain ⟨s', rfl⟩ := e.surjective s
    rcases s' with s' | t
    · rw [hWl, ← AlgHom.comp_apply, hfi]
      simp [WPres.z, WPres.origin_π]
    · obtain ⟨a, b, ⟨s, hs⟩ | ⟨v, hv⟩⟩ := hWr t
      · rw [hs, map_sub, AlgHom.commutes, ← Lift.map_hom, hfr]
        simp
      · have hab := congrFun (congrFun (hfα v) a) b
        rw [Matrix.map_apply] at hab
        rw [hv, Matrix.sub_apply, map_sub, hab, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
  have hC : ∀ x : O, (C x : MvPowerSeries W.σ O) = algebraMap O (MvPowerSeries W.σ O) x := by
    intro x
    simp [MvPowerSeries.algebraMap_apply]
  let cc : MvPowerSeries W.σ O →ₐ[O] O :=
    AlgHom.mk (MvPowerSeries.constantCoeff (R := O) (σ := W.σ)) (fun x => by simp [MvPowerSeries.algebraMap_apply])
  have hcc : ∀ g, f (W.π g) = constantCoeff g := by
    obtain ⟨G, -, huniq⟩ := co_ev O O O W.σ (AlgHom.id O O) (fun _ => 0) (fun _ => Ideal.zero_mem _)
    have h1 : f.comp W.π = G := huniq _ ⟨fun x => by
      rw [AlgHom.comp_apply, hC, AlgHom.commutes, AlgHom.commutes]
      rfl, fun s => hz s⟩
    have h2' : cc = G := huniq _ ⟨fun x => by simp [cc], fun s => by simp [cc]⟩
    intro g
    have := congrArg (fun φ => φ g) (h1.trans h2'.symm)
    simpa [cc] using this
  have hO : W.HasOrigin := by
    intro g hg
    rw [← hcc, hg, map_zero]
  have horig : W.origin hO = f := by
    ext x
    obtain ⟨g, rfl⟩ := W.surj x
    rw [WPres.origin_π, hcc]
  refine ⟨hO, ?_, ?_, ?_⟩
  · rw [horig, hfr]
  · intro v
    rw [horig, hfα]
  · rw [horig, hfi]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhGroup
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

open Matrix in
private theorem conj_form {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] {J A A' h : Matrix ι ι R} {ν : R}
    (e1 : A * A' = 1) (hA : Aᵀ * J * A = ν • J) (hh : hᵀ * J * h = J) :
    (A * h * A')ᵀ * J * (A * h * A') = J := by
  have e2 : A'ᵀ * Aᵀ = 1 := by rw [← transpose_mul, e1, transpose_one]
  calc (A * h * A')ᵀ * J * (A * h * A') = A'ᵀ * (hᵀ * (Aᵀ * J * A) * h) * A' := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = A'ᵀ * (Aᵀ * J * A) * A' := by
        rw [hA, mul_smul_comm, smul_mul_assoc, hh]
    _ = (A'ᵀ * Aᵀ) * J * (A * A') := by simp only [Matrix.mul_assoc]
    _ = J := by rw [e1, e2, one_mul, mul_one]

private theorem triple_ne {R ι : Type} [CommRing R] [Fintype ι] {A Y B : Matrix ι ι R} {a b : ι}
    (hab : (A * Y * B) a b ≠ 0) : ∃ c d, A a c ≠ 0 ∧ Y c d ≠ 0 ∧ B d b ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Qk1.triple_ne hab

private theorem blk_inv {R ι κ : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (blk : ι → κ) {h h' : Matrix ι ι R}
    (e1 : h * h' = 1) (e2 : h' * h = 1) (hb : ∀ a b, blk a ≠ blk b → h a b = 0) :
    ∀ a b, blk a ≠ blk b → h' a b = 0 := by
  classical
  intro a b hab
  set E : Matrix ι ι R := Matrix.diagonal fun x => if blk x = blk a then 1 else 0 with hE
  have h1 : E * h = h * E := by
    ext x y
    rw [hE, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hxy : blk x = blk y
    · rw [hxy, mul_comm]
    · rw [hb x y hxy, mul_zero, zero_mul]
  have h2 : h' * E = E * h' := by
    calc h' * E = h' * (E * h) * h' := by rw [mul_assoc, mul_assoc, e1, mul_one]
      _ = E * h' := by rw [h1, ← mul_assoc, e2, one_mul]
  have h3 := congrFun (congrFun h2 a) b
  rw [hE, Matrix.diagonal_mul, Matrix.mul_diagonal, if_neg (Ne.symm hab), if_pos rfl, mul_zero, one_mul] at h3
  exact h3.symm

private theorem map_mul_alg {O R S ι : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    [Fintype ι] [DecidableEq ι] (f : R →ₐ[O] S) (A B : Matrix ι ι R) : (A * B).map f = A.map f * B.map f :=
  Matrix.map_mul (f := (f : R →+* S))

theorem UpperTheory.V.Alg.hh_group :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w) (R : Type) [CommRing R] [Algebra O R] [IsCO O R],
      Φ.HH (1 : Matrix ι ι R) ∧ (∀ h h' : Matrix ι ι R, Φ.HH h → Φ.HH h' → Φ.HH (h * h')) ∧ (∀ h : Matrix ι ι R, Φ.HH h → ∃ h', Φ.HH h' ∧ h * h' = 1 ∧ h' * h = 1) ∧
      (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (h : Matrix ι ι R), Φ.HH h → Φ.HH (h.map f)) ∧
      (∀ (Γ : Type) [Group Γ] (r0 : Γ →* Matrix ι ι O), Φ.Normalises r0 → ∀ (s : Γ) (h : Matrix ι ι R), Φ.HH h → Φ.HH ((r0 s).map (algebraMap O R) * h * (r0 s⁻¹).map (algebraMap O R))) ∧
      ∀ (t : Multiplicative X →* Rˣ) (h : Matrix ι ι R), Φ.HH h → Φ.HH (Matrix.of fun a b => (t (Multiplicative.ofAdd (w a - w b)) : R) * h a b) := by
  intro O _ _ ι X _ _ _ w Φ R _ _ _
  refine ⟨⟨by simp, fun a b hab => Matrix.one_apply_ne fun e => hab (by rw [e]), by simp⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro h h' ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨?_, fun a b hab => ?_, by rw [map_mul_alg, a3, b3, one_mul]⟩
    · calc (h * h').transpose * Φ.JR R * (h * h') = h'.transpose * (h.transpose * Φ.JR R * h) * h' := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = Φ.JR R := by rw [a1, b1]
    · rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : Φ.blk a = Φ.blk c
      · rw [b2 c b (hc ▸ hab), mul_zero]
      · rw [a2 a c hc, zero_mul]
  · rintro h ⟨a1, a2, a3⟩
    have hJ : IsUnit (Φ.JR R) := Φ.unit.map (algebraMap O R).mapMatrix
    obtain ⟨K, hK⟩ := hJ.exists_left_inv
    have e2 : (K * h.transpose * Φ.JR R) * h = 1 := by
      rw [mul_assoc K, mul_assoc K, a1, hK]
    generalize K * h.transpose * Φ.JR R = h' at e2
    have e1 : h * h' = 1 := mul_eq_one_comm.1 e2
    refine ⟨h', ⟨?_, blk_inv Φ.blk e1 e2 a2, ?_⟩, e1, e2⟩
    · have := conj_form (h := h) (ν := (1 : R)) e1 (by rw [a1, one_smul]) a1
      calc h'.transpose * Φ.JR R * h' = h'.transpose * (h.transpose * Φ.JR R * h) * h' := by rw [a1]
        _ = (h * h').transpose * Φ.JR R * (h * h') := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = Φ.JR R := by rw [e1]; simp
    · have := congrArg (fun A : Matrix ι ι R => A.map (res O R)) e1
      simp only [map_mul_alg, a3, one_mul] at this
      rw [this]; simp
  · rintro R' _ _ _ f h ⟨a1, a2, a3⟩
    have hJ : Φ.JR R' = (Φ.JR R).map f := by
      ext a b; simp [FormData.JR]
    refine ⟨?_, fun a b hab => by simp [a2 a b hab], ?_⟩
    · rw [hJ, ← Matrix.transpose_map, ← map_mul_alg, ← map_mul_alg, a1]
    · rw [← a3]
      ext a b
      simp only [Matrix.map_apply, res_map]
  · rintro Γ _ r0 ⟨h1, ⟨π, h2⟩, -⟩ s h ⟨a1, a2, a3⟩
    have e1 : (r0 s).map (algebraMap O R) * (r0 s⁻¹).map (algebraMap O R) = 1 := by
      rw [← Matrix.map_mul, ← map_mul, mul_inv_cancel, map_one]; simp
    refine ⟨?_, fun a b hab => ?_, ?_⟩
    · obtain ⟨ν, hν⟩ := h1 s
      refine conj_form (ν := algebraMap O R ν) e1 ?_ a1
      have hO : Φ.JR O = Φ.J := by ext a b; simp [FormData.JR]
      rw [hO] at hν
      rw [FormData.JR, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hν]
      ext a b; simp
    · by_contra hne
      obtain ⟨c, d, k1, k2, k3⟩ := triple_ne hne
      have k1' : r0 s a c ≠ 0 := fun e => k1 (by simp [e])
      have k3' : r0 s⁻¹ d b ≠ 0 := fun e => k3 (by simp [e])
      have k4 : Φ.blk c = Φ.blk d := by_contra fun n => k2 (a2 c d n)
      apply hab
      rw [h2 s a c k1', k4, h2 s⁻¹ d b k3', map_inv]
      simp
    · rw [map_mul_alg, map_mul_alg, a3, mul_one, ← map_mul_alg, e1]; simp
  · rintro t h ⟨a1, a2, a3⟩
    refine ⟨?_, fun a b hab => by simp [a2 a b hab], ?_⟩
    · have e : (Matrix.of fun a b => (t (Multiplicative.ofAdd (w a - w b)) : R) * h a b) =
          Matrix.diagonal (fun a => (t (Multiplicative.ofAdd (w a)) : R)) * h *
            Matrix.diagonal (fun a => (t (Multiplicative.ofAdd (-w a)) : R)) := by
        ext a b
        rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, sub_eq_add_neg, ofAdd_add, map_mul,
          Units.val_mul]
        ring
      rw [e]
      refine conj_form (ν := (t (Multiplicative.ofAdd Φ.c) : R)) ?_ ?_ a1
      · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext a
        rw [← Units.val_mul, ← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero, map_one, Units.val_one]
      · ext a b
        rw [Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
        by_cases hJ : Φ.J a b = 0
        · simp [FormData.JR, hJ]
        · rw [← Φ.hw a b hJ, ofAdd_add, map_mul, Units.val_mul]
          ring
    · ext a b
      have k := congrFun (congrFun a3 a) b
      rw [Matrix.map_apply] at k
      rw [Matrix.map_apply, Matrix.of_apply, map_mul, k]
      by_cases hab : a = b
      · subst hab; simp
      · simp [Matrix.one_apply_ne hab]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivCond
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem lift_map_map' {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    {R R' R'' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']
    [CommRing R''] [Algebra O R''] [IsCO O R''] (f : R →ₐ[O] R') (g : R' →ₐ[O] R'')
    (r : Lift O rbar R) : Lift.map g (Lift.map f r) = Lift.map (g.comp f) r := by
  apply Lift.ext
  ext x a b
  rfl

theorem UpperTheory.V.Alg.univ_cond :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (Γ ι : Type) [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rbar R) (P₀ P : Cond O rbar), Represents P₀ r → P.IsClosed → (∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra O R₁) (_ : IsCO O R₁) (r₁ : Lift O rbar R₁), P₀ R₁ r₁ ∧ P R₁ r₁) →
      ∃ (R' : Type) (_ : CommRing R') (_ : Algebra O R') (_ : IsCO O R') (p : R →ₐ[O] R'), Function.Surjective p ∧ Represents (fun C _ _ _ s => P₀ C s ∧ P C s) (r.map p) := by
  intro O _ _ Γ ι _ _ _ _ rbar R _ _ _ r P₀ P hrep hcl hex
  obtain ⟨I, hI⟩ := hcl R r
  obtain ⟨R₁, _, _, _, r₁, h0, h1⟩ := hex
  obtain ⟨f, hf, -⟩ := (hrep R₁).2 r₁ h0
  have hf1 : P R₁ (Lift.map f r) := hf ▸ h1
  have hfI : ∀ x ∈ I, f x = 0 := (hI R₁ f).1 hf1
  set J : Ideal R := Ideal.span I
  have hJf : ∀ x ∈ J, f x = 0 := by
    intro x hx
    have hle : J ≤ RingHom.ker f.toRingHom := Ideal.span_le.2 (fun y hy => hfI y hy)
    exact hle hx
  have hJ : J ≠ ⊤ := by
    intro htop
    have h1mem : (1 : R) ∈ J := htop ▸ Submodule.mem_top
    have := hJf 1 h1mem
    simp at this
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  haveI hco : IsCO O (R ⧸ J) := co_quot O R (R ⧸ J) (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)
  have hpI : ∀ x ∈ I, Ideal.Quotient.mkₐ O J x = 0 := by
    intro x hx
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span hx
  refine ⟨R ⧸ J, inferInstance, inferInstance, hco, Ideal.Quotient.mkₐ O J, Ideal.Quotient.mkₐ_surjective O J, ?_⟩
  intro R'' _ _ _
  refine ⟨fun g => ?_, fun r' hr' => ?_⟩
  · rw [lift_map_map']
    refine ⟨(hrep R'').1 _, (hI R'' _).2 ?_⟩
    intro x hx
    rw [AlgHom.comp_apply, hpI x hx, map_zero]
  · obtain ⟨f', hf', huniq⟩ := (hrep R'').2 r' hr'.1
    have hf'I : ∀ x ∈ I, f' x = 0 := (hI R'' f').1 (hf' ▸ hr'.2)
    have hf'J : ∀ x ∈ J, f' x = 0 := by
      intro x hx
      have hle : J ≤ RingHom.ker f'.toRingHom := Ideal.span_le.2 (fun y hy => hf'I y hy)
      exact hle hx
    refine ⟨Ideal.Quotient.liftₐ J f' hf'J, ?_, ?_⟩
    · show Lift.map _ (Lift.map _ r) = r'
      rw [lift_map_map', Ideal.Quotient.liftₐ_comp]
      exact hf'
    · intro g hg
      apply Ideal.Quotient.algHom_ext O
      rw [Ideal.Quotient.liftₐ_comp]
      apply huniq
      show Lift.map _ r = r'
      rw [← lift_map_map']
      exact hg
end

