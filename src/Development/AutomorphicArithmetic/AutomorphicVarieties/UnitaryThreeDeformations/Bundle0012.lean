module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Adjoin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CzBasic
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

private theorem dvr_norm {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (f : A →+* PadicAlgCl l) (hle : ∀ x, ‖f x‖ ≤ 1) :
    (∀ u : A, IsUnit u → ‖f u‖ = 1) ∧
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ (n : ℕ) (x : A), x ∈ maximalIdeal A ^ n → ‖f x‖ ≤ q ^ n := by
  have hu : ∀ u : Aˣ, ‖f u‖ = 1 := by
    intro u
    have h1 : ‖f u‖ * ‖f ((u⁻¹ : Aˣ) : A)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv]; simp
    have h2 := hle u
    have h3 := hle (u⁻¹ : Aˣ)
    have h4 := norm_nonneg (f u)
    nlinarith
  refine ⟨fun u ⟨v, hv⟩ => hv ▸ hu v, ?_⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hl0 : (l : A) ≠ 0 := by
    intro h
    have h' : f l = 0 := by rw [h, map_zero]
    have : (l : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have hl : ‖f l‖ < 1 := by
    have : f l = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  refine ⟨‖f ϖ‖, norm_nonneg _, ?_, fun n x hx => ?_⟩
  · obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
    rw [h, map_mul, norm_mul, hu, one_mul, map_pow, norm_pow] at hl
    by_contra hc
    exact absurd hl (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))
  · rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [map_mul, norm_mul, map_pow, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hle y)

private theorem conjBy_conjBy {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (h k : GL (Fin 3) R) :
    conjBy h (conjBy k r) = conjBy (h * k) r := by
  refine MonoidHom.ext fun g => ?_
  simp [conjBy, mul_assoc]

private theorem conjBy_one {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) :
    conjBy 1 r = r := by
  refine MonoidHom.ext fun g => ?_
  simp [conjBy]

private theorem aux {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra O (PadicAlgCl l)]
    {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ]
    (F : Frame O G Γ ι) (hF : F.Ok) (g₁ : Γ) (hg : F.Marked g₁) (r : Γ →* GG (m := 3) (R := PadicAlgCl l))
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra O A]
    (f : A →ₐ[O] PadicAlgCl l) (hle : ∀ x, ‖f x‖ ≤ 1) (t : (PadicAlgCl l)ˣ) (r' : Γ →* GG (m := 3) (R := A))
    (hpt : F.IsPt g₁ r') (hp : push f r' = conjBy (tor _ t) r) :
    HasMult F.η r ∧ Normalised F.c g₁ r ∧ Continuous (mats r) ∧
      ‖zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l))‖ < 1 ∧ ‖zeta F.c g₁ r‖ = 1 ∧
      (∀ g a, ‖(r g).mat a a - (F.rz (PadicAlgCl l) g).mat a a‖ < 1) := by
  obtain ⟨hu, q, hq0, hq1, hq⟩ := dvr_norm (f : A →+* PadicAlgCl l) hle
  simp only [RingHom.coe_coe] at hu hq
  have hr : r = conjBy (tor _ t⁻¹) (push f r') := by
    rw [hp, conjBy_conjBy, ← map_mul, inv_mul_cancel, map_one, conjBy_one]
  obtain ⟨c1, c2, c3, -, -⟩ := conjBy_tor (push f r') t⁻¹
  rw [← hr] at c1 c2 c3
  have hent : ∀ g a b, (push f r' g).mat a b = f ((r' g).mat a b) := fun _ _ _ => rfl
  have hrz : ∀ g a b, (F.rz (PadicAlgCl l) g).mat a b = algebraMap O _ ((r0 F.η F.Ψ g).mat a b) := fun _ _ _ => rfl
  have hdiag : ∀ g a, ‖(r g).mat a a - (F.rz (PadicAlgCl l) g).mat a a‖ < 1 := by
    intro g a
    have h := hq 1 _ (by rw [pow_one]; exact hpt.red g a a)
    rw [pow_one, Matrix.sub_apply, map_sub, Matrix.map_apply, AlgHom.commutes] at h
    rw [c1, hent, hrz]
    simp only [wt, sub_self, zpow_zero, Units.val_one, one_mul]
    exact lt_of_le_of_lt h hq1
  have hz : ‖zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l))‖ < 1 := by
    have e : zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l)) =
        ((r g₁).mat 0 0 - (F.rz (PadicAlgCl l) g₁).mat 0 0) +
          -((r (gstar F.c g₁)).mat 0 0 - (F.rz (PadicAlgCl l) (gstar F.c g₁)).mat 0 0) := by
      simp only [zeta, zmat, Matrix.sub_apply]; ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (hdiag _ _) ?_)
    rw [norm_neg]; exact hdiag _ _
  have hz0 : ‖zeta F.c g₁ (F.rz (PadicAlgCl l))‖ = 1 := by
    have h0 := (zeta_reducible_rep_eq_sub_inv_and_isUnit F.η F.Ψ F.c g₁ ⟨hF.csq, hF.ηc, hF.Ψc, hg.1, hg.2⟩).2
    rw [← hu _ (h0.map (algebraMap O A)), AlgHom.commutes]
    simp only [zeta, zmat, Matrix.sub_apply, map_sub, hrz]
  refine ⟨fun g => (c2 g).trans (hpt.mult g), c3 _ _ ⟨?_, ?_, ?_⟩, ?_, hz, ?_, hdiag⟩
  · ext a b
    rw [hent, hpt.norm.atc]
    simp [Matrix.one_apply, apply_ite f]
  · have h := congrArg f hpt.norm.z12
    simpa only [zmat, Matrix.sub_apply, map_sub, map_zero, hent] using h
  · have h := congrArg f hpt.norm.z21
    simpa only [zmat, Matrix.sub_apply, map_sub, map_zero, hent] using h
  · refine continuous_matrix fun a b => ?_
    simp only [mats, c1, hent]
    refine continuous_const.mul (continuous_iff_continuousAt.2 fun g => ?_)
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hq1
    filter_upwards [(hpt.cont n).eventually_eq g] with g' hg'
    have h := congrFun (congrFun hg' a) b
    rw [Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq] at h
    rw [dist_eq_norm, ← map_sub]
    exact lt_of_le_of_lt (hq n _ h) hn
  · have e : zeta F.c g₁ r = (zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l))) + zeta F.c g₁ (F.rz (PadicAlgCl l)) := by
      ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hz0]; exact hz.ne), hz0]
    exact max_eq_right hz.le

theorem UpperTheory.V.UnitaryThreeInertia.isCharZeroPt_basic :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ g₁, F.Marked g₁ → ∀ (r : Γ →* GG (m := 3) (R := PadicAlgCl l)), F.IsCharZeroPt g₁ r → HasMult F.η r ∧ Normalised F.c g₁ r ∧ Continuous (mats r) ∧ ‖zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l))‖ < 1 ∧ ‖zeta F.c g₁ r‖ = 1 ∧
      (∀ g a, ‖(r g).mat a a - (F.rz (PadicAlgCl l) g).mat a a‖ < 1) ∧ ∀ t, F.IsCharZeroPt g₁ (conjBy (tor (PadicAlgCl l) t) r) := by
  intro l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg r hr
  obtain ⟨A, hA, hfin, t, r', hpt, hp⟩ := hr
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := aux F hF g₁ hg r A.val (fun x =>
    norm_le_one_of_int l _ (isIntegral_trans (A := O) _ ((Algebra.IsIntegral.isIntegral (R := O) x).map A.val)))
    t r' hpt hp
  refine ⟨h1, h2, h3, h4, h5, h6, fun s => ⟨A, hA, hfin, t * s⁻¹, r', hpt, ?_⟩⟩
  rw [conjBy_conjBy, ← map_mul, inv_mul_cancel_right, hp]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GlobalEulerCharacteristicRationalsOddPrime
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

private noncomputable def subquotEquiv {R R' X : Type*} [CommRing R] [CommRing R'] [AddCommGroup X]
    [Module R X] [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    (Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype) :=
  Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => by
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
    exact hB _

theorem UpperTheory.global_euler_characteristic_rationals_odd_prime :
    GlobalFiniteness → GlobalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset Pl) (ρ : Representation k (Gam Ω S) M),
        ContainsAbove S l → ContAction ρ → ∀ σ : Formalism.ConjugateSelfDual.G ℚ Ω, IsCC σ →
        Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧
          finrank k (H1 ρ) + finrank k (LinearMap.ker (ρ (toGS Ω _ σ) - LinearMap.id)) = finrank k (H0 ρ) + finrank k (H2 ρ) + finrank k M := by
  intro hF hE Ω _ _ _ l _ hl k M _ _ _ _ _ _ _ _ S ρ hS hρ σ hσ
  haveI : CharP k (l ^ 1) := by rw [pow_one]; infer_instance
  letI : Module (ZMod (l ^ 1)) M := Module.compHom _ (ZMod.castHom (dvd_refl _) k)
  let ρ' : Representation (ZMod (l ^ 1)) (Gam Ω S) M :=
    { toFun := fun g =>
        { toFun := ρ g
          map_add' := map_add (ρ g)
          map_smul' := fun c m => map_smul (ρ g) (ZMod.castHom (dvd_refl _) k c) m }
      map_one' := LinearMap.ext fun m => show ρ 1 m = m by rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => show ρ (g * h) m = ρ g (ρ h m) by
        rw [map_mul]; rfl }
  have e0 : H0 ρ ≃ H0 ρ' := Equiv.subtypeEquivRight fun _ => Iff.rfl
  have e1 : H1 ρ ≃ H1 ρ' := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have e2 : H2 ρ ≃ H2 ρ' := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have ec : LinearMap.ker (ρ (toGS Ω _ σ) - LinearMap.id) ≃ {m : M // ρ' (toGS Ω _ σ) m = m} :=
    Equiv.subtypeEquivRight fun m => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      exact Iff.rfl
  obtain ⟨-, f1, f2, -⟩ := hF ℚ Ω l 1 M S ρ' one_pos hS hρ
  have h := UpperTheory.card_global_euler_characteristic_rationals hE Ω l hl M S ρ' hS hρ σ hσ
  haveI : Finite (H1 ρ) := Finite.of_equiv _ e1.symm
  haveI : Finite (H2 ρ) := Finite.of_equiv _ e2.symm
  haveI : Module.Finite k M := Module.Finite.of_finite
  haveI : Module.Finite k (H1 ρ) := Module.Finite.of_finite
  haveI : Module.Finite k (H2 ρ) := Module.Finite.of_finite
  have hk : 1 < Nat.card k := Finite.one_lt_card
  refine ⟨inferInstance, inferInstance, ?_⟩
  apply Nat.pow_right_injective hk
  beta_reduce
  rw [pow_add, pow_add, pow_add, ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank,
    ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank,
    Nat.card_congr e0, Nat.card_congr e1, Nat.card_congr e2, Nat.card_congr ec]
  exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsPtHomAct
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem exists_act {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ]
    {R : Type} [CommRing R] [Algebra O R] (u : Γ →* GG (m := 3) (R := R)) (W : WPres O ℤ R)
    (hW : ∀ j, W.part j = wpart O u j) {K : Type} [CommRing K] [Algebra O K] (ξ : Sring (O := O) u →ₐ[O] K) (t : Kˣ) :
    ∃ ξt : Sring (O := O) u →ₐ[O] K, ∀ (j : ℤ) x (hx : x ∈ wpart O u j),
      ξt ⟨x, mem_Sring u hx⟩ = ((t ^ j : Kˣ) : K) * ξ ⟨x, mem_Sring u hx⟩ := by
  have hA : W.A = Sring (O := O) u := by
    ext x
    show x ∈ ⨆ j, W.part j ↔ x ∈ ⨆ j, wpart O u j
    simp only [hW]
  refine ⟨(act W.gr (zpowersHom Kˣ t) (ξ.comp (Subalgebra.inclusion hA.le))).comp
    (Subalgebra.inclusion hA.ge), fun j x hx => ?_⟩
  have hx' : Subalgebra.inclusion hA.ge ⟨x, mem_Sring u hx⟩ ∈ W.gr j := by
    show x ∈ W.part j
    rwa [hW]
  rw [AlgHom.comp_apply, act_of_mem W.gr _ _ hx']
  rfl

theorem UpperTheory.V.UnitaryThreeInertia.isPtHom_act :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
      (u : Γ →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
    Module.Finite O (wpart O u 0) →
    ∀ (ξ : Sring (O := O) u →ₐ[O] (PadicAlgCl l)) (r : Γ →* GG (m := 3) (R := PadicAlgCl l)), IsPtHom u ξ r →
    ∀ (ξ' : Sring (O := O) u →ₐ[O] (PadicAlgCl l)) (t : (PadicAlgCl l)ˣ), IsPtHom u ξ' (conjBy (tor (PadicAlgCl l) t) r) ↔
      ∀ (j : ℤ) x (hx : x ∈ wpart O u j), ξ' ⟨x, mem_Sring u hx⟩ = ((t ^ j : (PadicAlgCl l)ˣ) : (PadicAlgCl l)) * ξ ⟨x, mem_Sring u hx⟩ := by
  intro l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg R _ _ _ u hu hfin ξ r hr ξ' t
  obtain ⟨hm, hri, -⟩ := conjBy_tor r t
  constructor
  · intro h
    obtain ⟨W, hW, -⟩ := exists_adapted F hF g₁ hg u hu
    obtain ⟨ξt, hξt⟩ := exists_act u W hW.part ξ t
    have e : ξ' = ξt := by
      refine AlgHom.ext_of_eq_adjoin (sring_eq_adjoin F hF g₁ hg u hu hfin).1 ?_
      rintro _ ⟨g, a, b, -, rfl⟩
      refine Eq.trans ?_ (hξt _ _ (entry_mem u g a b)).symm
      have h1 := congrFun (congrFun (h g).2 a) b
      rw [hm, (hr g).2] at h1
      exact h1.symm
    rw [e]
    exact hξt
  · intro h g
    refine ⟨(hri g).trans (hr g).1, ?_⟩
    ext a b
    rw [hm, (hr g).2]
    exact (h _ _ (entry_mem u g a b)).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.UnitEqOneOfPowEqOneOfResidueOne
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia

private theorem conjBy_one_inv_eq_self {R D : Type} [CommRing R] [Group D] (r : D →* GG (m := 3) (R := R)) :
    conjBy (1 : GL (Fin 3) R)⁻¹ r = r := by
  ext1 g
  simp [conjBy]

private theorem rep_mul_matrix_of_trivial_sign {R D : Type} [CommRing R] [Group D] (r : D →* GG (m := 3) (R := R)) (g h : D) (hg : (r g).right = 1) :
    (r (g * h)).mat = (r g).mat * (r h).mat := by
  simp [GG.mat, hg]

private theorem diagonal_mul_diag_entry {R : Type} [CommRing R] {X : Matrix (Fin 3) (Fin 3) R} (hX : X.IsDiag)
    (Y : Matrix (Fin 3) (Fin 3) R) (a : Fin 3) : (X * Y) a a = X a a * Y a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a (fun c _ hc => by rw [hX hc.symm, zero_mul])
    (fun hn => absurd (Finset.mem_univ a) hn)]

private def kap {R D : Type} [CommRing R] [Group D] (η : D →* ℤˣ) (r : D →* GG (m := 3) (R := R)) (hm : HasMult η r)
    (hd : ∀ g, η g = 1 → (r g).mat.IsDiag) (a : Fin 3) : η.ker →* R where
  toFun g := (r g).mat a a
  map_one' := by simp [GG.mat]
  map_mul' g h := by
    rw [Subgroup.coe_mul, rep_mul_matrix_of_trivial_sign r _ _ ((hm g).trans g.2), diagonal_mul_diag_entry (hd g g.2)]

private theorem unit_eq_one_of_pow_eq_one_of_residue_one {R : Type} [CommRing R] [IsLocalRing R] (u : Rˣ) (N : ℕ) (hN : IsUnit (N : R))
    (h1 : (u : R) - 1 ∈ maximalIdeal R) (h2 : u ^ N = 1) : u = 1 := by
  have e := mul_geom_sum (u : R) N
  rw [← Units.val_pow_eq_pow_val, h2, Units.val_one, sub_self] at e
  have hu : residue R (u : R) = 1 := by
    have := (residue_eq_zero_iff _).2 h1
    rwa [map_sub, map_one, sub_eq_zero] at this
  have hs : IsUnit (∑ i ∈ Finset.range N, (u : R) ^ i) := by
    rw [← residue_ne_zero_iff_isUnit] at hN ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, hu] using hN
  exact Units.ext (sub_eq_zero.1 (hs.mul_left_eq_zero.1 e))

private theorem apply_eq_of_hasMult_of_mat_eq {R D : Type} [CommRing R] [Group D] {η : D →* ℤˣ} {r ρ : D →* GG (m := 3) (R := R)} (hm : HasMult η r)
    (hm' : HasMult η ρ) (g : D) (h : (r g).mat = (ρ g).mat) : r g = ρ g :=
  SemidirectProduct.ext (Units.ext h) ((hm g).trans (hm' g).symm)

private theorem diag_entry_eq_character_on_inertia {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [Group D]
    {η : D →* ℤˣ} {Ψ : D →* Oˣ} {I : Subgroup D} {r : D →* GG (m := 3) (R := R)} (hr : Red η Ψ r)
    (hd : ∀ g, η g = 1 → (r g).mat.IsDiag) (hx : ∃ x, η x = 1 ∧ IsUnit ((Ψ x : O) ^ 2 - 1)) (hT : CondT η Ψ I r)
    (s : D) (hs : s ∈ I) (hη : η s = 1) (a : Fin 3) : (r s).mat a a = algebraMap O R (psi Ψ a s) := by
  obtain ⟨x, hx, hx'⟩ := hx
  have hc : Canon (r x).mat 1 := ⟨fun a b => by simp, fun a => by simp, by simpa using hd x hx⟩
  have := ((cond_iff_canon η Ψ I r x 1 hr hx hx' hc).1.1 hT).ine s hs hη a
  rwa [conjBy_one_inv_eq_self] at this

private theorem diagonal_reps_eq_of_same_frame_point {O R G Γ ι : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ] (F : Frame O G Γ ι) (hF : F.Ok) (hC : F.Cl1) (g₁ : Γ)
    (r ρ : Γ →* GG (m := 3) (R := R)) (hr : F.IsPt g₁ r) (hρ : F.IsPt g₁ ρ) (hd : ∀ g, F.η g = 1 → (r g).mat.IsDiag)
    (hd' : ∀ g, F.η g = 1 → (ρ g).mat.IsDiag) : r = ρ := by
  classical
  let u : Fin 3 → (F.η.ker →* Rˣ) := fun a =>
    (kap F.η r hr.mult hd a).toHomUnits / (kap F.η ρ hρ.mult hd' a).toHomUnits
  have hu : ∀ a (g : F.η.ker), (u a g : R) * (ρ g).mat a a = (r g).mat a a := fun a g => by
    show (((kap F.η r hr.mult hd a).toHomUnits g / (kap F.η ρ hρ.mult hd' a).toHomUnits g : Rˣ) : R) *
      (((kap F.η ρ hρ.mult hd' a).toHomUnits g : Rˣ) : R) = ((kap F.η r hr.mult hd a).toHomUnits g : Rˣ)
    rw [← Units.val_mul, div_mul_cancel]
  have hun : ∀ a (g : F.η.ker), IsUnit ((ρ g).mat a a) := fun a g =>
    ((kap F.η ρ hρ.mult hd' a).toHomUnits g).isUnit
  have h1 : ∀ (g : F.η.ker), r g = ρ g → ∀ a, u a g = 1 := fun g e a => by
    apply Units.ext
    apply (hun a g).mul_right_cancel
    rw [hu, e, Units.val_one, one_mul]
  have h2 : ∀ (g : F.η.ker), (∀ a, (r g).mat a a = (ρ g).mat a a) → r g = ρ g := fun g e => by
    refine apply_eq_of_hasMult_of_mat_eq hr.mult hρ.mult _ ?_
    ext a b
    by_cases hab : a = b
    · subst hab; exact e a
    · rw [hd g g.2 hab, hd' g g.2 hab]
  have h2' : ∀ (g : F.η.ker), (∀ a, u a g = 1) → r g = ρ g := fun g e =>
    h2 g fun a => by rw [← hu, e, Units.val_one, one_mul]
  have hc : r F.c = ρ F.c := apply_eq_of_hasMult_of_mat_eq hr.mult hρ.mult _ (hr.norm.atc.trans hρ.norm.atc.symm)
  have hI : ∀ v (s : F.D v), s ∈ F.Iv v → F.η (F.loc v s) = 1 → r (F.loc v s) = ρ (F.loc v s) := by
    intro v s hs hη
    by_cases hv : v ∈ F.Tb
    · have key : ∀ r : Γ →* GG (m := 3) (R := R), F.IsPt g₁ r → (∀ g, F.η g = 1 → (r g).mat.IsDiag) → ∀ a,
          (r (F.loc v s)).mat a a = algebraMap O R (psi (F.Ψv v) a s) := by
        intro r hr hd a
        refine diag_entry_eq_character_on_inertia (η := F.ηv v) (Ψ := F.Ψv v) (I := F.Iv v) (r := r.comp (F.loc v)) ⟨fun g => hr.mult (F.loc v g), fun g => hr.red (F.loc v g)⟩
          (fun g hg => hd (F.loc v g) hg) (hF.x v hv) ?_ s hs hη a
        rcases hv with hv | hv
        · exact (hr.loc v).1 hv
        · obtain ⟨h, hh, hD⟩ := (hr.loc v).2.1 hv
          exact ⟨h, hh, hD.toTriIn⟩
      exact h2 ⟨_, hη⟩ fun a => (key r hr hd a).trans (key ρ hρ hd' a).symm
    · haveI := Fintype.ofFinite (ResidueField O)
      have hmem : s ^ Fintype.card (ResidueField O)ˣ ∈ F.Nv v := by
        refine ⟨⟨pow_mem hs _, pow_mem (show s ∈ (F.ηv v).ker from hη) _⟩, ?_⟩
        show ((Units.map (residue O).toMonoidHom).comp (F.Ψv v)) _ = 1
        rw [map_pow, pow_card_eq_one]
      have hN : IsUnit ((Fintype.card (ResidueField O)ˣ : ℕ) : O) := by
        rw [← residue_ne_zero_iff_isUnit, map_natCast, Fintype.card_units,
          Nat.cast_sub Fintype.card_pos, FiniteField.cast_card_eq_zero]
        simp
      refine h2' ⟨_, hη⟩ fun a => unit_eq_one_of_pow_eq_one_of_residue_one _ (Fintype.card (ResidueField O)ˣ)
        (by simpa using hN.map (algebraMap O R)) ?_ ?_
      · have e1 := hr.red (F.loc v s) a a
        have e2 := hρ.red (F.loc v s) a a
        have e3 := sub_mem e1 e2
        rw [Matrix.sub_apply, Matrix.sub_apply, sub_sub_sub_cancel_right] at e3
        have e4 := hu a ⟨_, hη⟩
        rw [← Ideal.mul_unit_mem_iff_mem _ (hun a ⟨_, hη⟩), sub_mul, e4, one_mul]
        exact e3
      · rw [← map_pow]
        refine h1 _ ?_ a
        have e1 := (hr.loc v).2.2 hv _ hmem
        have e2 := (hρ.loc v).2.2 hv _ hmem
        rw [MonoidHom.comp_apply, map_pow (F.loc v)] at e1 e2
        exact e1.trans e2.symm
  have hsplit : ∀ g, F.η g = 1 ∨ ∃ g', F.η g' = 1 ∧ g = g' * F.c := fun g => by
    rcases Int.units_eq_one_or (F.η g) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨g * F.c, by simp [h, hF.ηc], by rw [mul_assoc, hF.csq, mul_one]⟩
  have hconj : ∀ a (g x : Γ) (hg : F.η g = 1) (hx : F.η x = 1) (h : g * x * g⁻¹ ∈ F.η.ker), r x = ρ x →
      u a ⟨_, h⟩ = 1 := by
    intro a g x hg hx h e
    have : (⟨_, h⟩ : F.η.ker) = ⟨g, hg⟩ * ⟨x, hx⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, h1 ⟨x, hx⟩ e a, map_inv, mul_one, mul_inv_cancel]
  have hker : ∀ g : F.η.ker, r g = ρ g := by
    intro g
    refine h2' g fun a => Units.ext ?_
    rw [← sub_eq_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) Ideal.IsPrime.ne_top',
      Submodule.mem_iInf]
    intro n
    let q : R →* R ⧸ maximalIdeal R ^ n := (Ideal.Quotient.mk (maximalIdeal R ^ n)).toMonoidHom
    have lc : ∀ (r : Γ →* GG (m := 3) (R := R)) (hr : F.IsPt g₁ r) (hd : ∀ g, F.η g = 1 → (r g).mat.IsDiag),
        IsLocallyConstant fun g => Units.map q ((kap F.η r hr.mult hd a).toHomUnits g) := fun r hr hd =>
      IsLocallyConstant.desc _ Units.val
        (((hr.cont n).comp fun X => X a a).comp_continuous continuous_subtype_val) Units.val_injective
    have hχ := hC _ ((Units.map q).comp (u a)) (by
      have := (lc r hr hd).div (lc ρ hρ hd')
      convert this using 1
      funext g
      exact map_div (Units.map q) _ _) (by
      intro v s g h hs
      have hη : F.η (F.loc v s) = 1 := by
        have : F.η (g * F.loc v s * g⁻¹) = 1 := h
        rwa [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at this
      have e := hI v s hs hη
      rw [MonoidHom.comp_apply]
      rcases hsplit g with hg | ⟨g', hg, rfl⟩
      · rw [hconj a g _ hg hη h e, map_one]
      · have e0 : g' * F.c * F.loc v s * (g' * F.c)⁻¹ = g' * (F.c * F.loc v s * F.c⁻¹) * g'⁻¹ := by group
        have := hconj a g' (F.c * F.loc v s * F.c⁻¹) hg (by simp [hη]) (e0 ▸ h) (by simp only [map_mul, map_inv, hc, e])
        rw [show (⟨_, h⟩ : F.η.ker) = ⟨_, e0 ▸ h⟩ from Subtype.ext e0, this, map_one])
    have := congrArg Units.val (DFunLike.congr_fun hχ g)
    rw [← Ideal.Quotient.eq]
    exact this
  ext1 g
  rcases hsplit g with hg | ⟨g', hg, rfl⟩
  · exact hker ⟨g, hg⟩
  · rw [map_mul, map_mul, hc, hker ⟨g', hg⟩]

end UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.eq_rz_of_diag :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.Cl1 → ∀ g₁, F.Marked g₁ → ∀ (r : Γ →* GG (m := 3) (R := PadicAlgCl l)), F.IsCharZeroPt g₁ r → Upper F.η r → Lower F.η r → r = F.rz (PadicAlgCl l) := by
  intro l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF hC g₁ _ r ⟨A, _, _, t, r', hp, he⟩ hU hL
  haveI : FaithfulSMul O A := (faithfulSMul_iff_algebraMap_injective O A).2 fun x y h =>
    FaithfulSMul.algebraMap_injective O (PadicAlgCl l) (congrArg Subtype.val h)
  have hz : ∀ (B : Type) [CommRing B] [Algebra O B] g, (F.rz B g).mat.IsDiag := by
    intro B _ _ g a b hab
    show algebraMap O B (((tor O (F.Ψ g) : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) a b) = 0
    rw [tor_val, Matrix.diagonal_apply_ne _ hab, map_zero]
  have hent : ∀ g a b, ((r' g).mat a b : PadicAlgCl l) =
      ((t ^ wt a b : (PadicAlgCl l)ˣ) : PadicAlgCl l) * (r g).mat a b := fun g a b => by
    rw [← (conjBy_tor r t).1, ← he]; rfl
  have hd : ∀ g, F.η g = 1 → (r' g).mat.IsDiag := by
    intro g hg a b hab
    apply Subtype.ext
    rw [hent]
    have : wt a b ≠ 0 := fun h => hab (by
      have h' : wt1 a = wt1 b := sub_eq_zero.1 h
      simp only [wt1] at h'
      apply Fin.ext; omega)
    rcases lt_or_gt_of_ne this with h | h
    · rw [hU g hg a b h, mul_zero]; rfl
    · rw [hL g hg a b h, mul_zero]; rfl
  haveI : IsNoetherianRing A := PrincipalIdealRing.isNoetherianRing
  haveI : IsLocalHom (algebraMap O A) := Algebra.IsIntegral.isLocalHom O A
  have e := diagonal_reps_eq_of_same_frame_point F hF hC g₁ r' (F.rz A) hp (isPt_rz F hF g₁) hd fun g _ => hz A g
  subst e
  ext1 g
  refine SemidirectProduct.ext (Units.ext ?_) ?_
  · show (r g).mat = (F.rz (PadicAlgCl l) g).mat
    ext a b
    have h := hent g a b
    by_cases hab : a = b
    · subst hab
      rw [wt, sub_self, zpow_zero, Units.val_one, one_mul] at h
      rw [← h]; rfl
    · rw [hz A g hab] at h
      rw [hz _ g hab]
      exact (Units.mul_right_eq_zero _).1 h.symm
  · rw [← (conjBy_tor r t).2.1, ← he]; rfl
end

