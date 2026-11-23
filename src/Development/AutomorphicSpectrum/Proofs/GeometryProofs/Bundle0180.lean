module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0034
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueUniqueBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0089
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0094
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0091
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0178
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0175
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0095
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0154
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0158
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModuleModNBasis
section
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.ModFree

open NumberField Module
open scoped nonZeroDivisors TensorProduct

theorem exists_map_of_basis {O B M Mb : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B]
    (S : Submonoid O) (hS : S ≤ O⁰) [IsLocalization S B] [AddCommGroup M] [Module O M]
    [AddCommGroup Mb] [Module O Mb] [Module B Mb] [IsScalarTower O B Mb] (f : M →ₗ[O] Mb)
    [IsLocalizedModule S f] {n : ℕ} (b : Basis (Fin n) B Mb) :
    ∃ φ : (Fin n → O) →ₗ[O] M, Function.Injective φ ∧
      ∀ m, ∃ s : S, ∃ y, (s : O) • m = φ y := by
  choose p hp using fun i => IsLocalizedModule.surj S f (b i)
  have hinj : Function.Injective (algebraMap O B) := IsLocalization.injective B hS
  refine ⟨Fintype.linearCombination O (fun i => (p i).1), ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [Fintype.linearCombination_apply] at hy
    have h1 : ∑ i, algebraMap O B (y i * (p i).2) • b i = 0 := by
      have h := congrArg f hy
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← hp i, Submonoid.smul_def, algebraMap_smul, mul_smul]
    have h2 := Fintype.linearIndependent_iff.mp b.linearIndependent _ h1
    funext i
    have h3 : y i * (p i).2 = 0 := hinj (by rw [h2 i, map_zero])
    exact (mul_eq_zero.mp h3).resolve_right (nonZeroDivisors.ne_zero (hS (p i).2.2))
  · intro x
    have hx := b.sum_repr (f x)
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples S Finset.univ
      (fun i => b.repr (f x) i * ((IsLocalization.map_units B (p i).2).unit⁻¹ : Bˣ))
    choose a ha using fun i => RingHom.mem_rangeS.mp (ht i (Finset.mem_univ i))
    have hc : ∀ i, algebraMap O B (a i) * algebraMap O B (p i).2 =
        algebraMap O B t * b.repr (f x) i := by
      intro i
      rw [ha i, Algebra.smul_def, mul_assoc, mul_assoc, IsUnit.val_inv_mul, mul_one]
    have key : f ((t : O) • x) = f (Fintype.linearCombination O (fun i => (p i).1) a) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, Fintype.linearCombination_apply, map_sum, ← hx, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← hp i, Submonoid.smul_def, ← algebraMap_smul B (a i),
        ← algebraMap_smul B ((p i).2 : O), smul_smul, hc i, mul_smul, algebraMap_smul]
    obtain ⟨c, hc'⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) key
    refine ⟨c * t, (c : O) • a, ?_⟩
    rw [map_smul, Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, hc', Submonoid.smul_def]

theorem exists_free_map_mod (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M]
    [Module (𝓞 E) M] : Module.Finite (𝓞 E) M → Module.Projective (𝓞 E) M →
    ∀ (n N : ℕ), Module.finrank (𝓞 E) M = n → 0 < N →
    ∃ φ : (Fin n → 𝓞 E) →ₗ[𝓞 E] M, (∀ m, ∃ x b, m = φ x + N • b) ∧
      ∀ x b, φ x = N • b → ∃ x', x = N • x' := by
  intro hfin hproj n N hn hN
  set S := GlobalTheory.PlaceInt.LocBasis.primeTo (𝓞 E) N with hSdef
  have hS : S ≤ (𝓞 E)⁰ := by
    rintro s ⟨k, hk0, -, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hk0)
  have : IsDomain (Localization S) := IsLocalization.isDomain_localization hS
  have : IsPrincipalIdealRing (Localization S) :=
    GlobalTheory.PlaceInt.LocBasis.isPrincipalIdealRing_loc E N hN hS (Localization S)
  have hrank : Module.finrank (Localization S) (LocalizedModule S M) = n := by
    rw [IsLocalization.finrank_eq (Localization S) S hS,
      IsLocalizedModule.finrank_eq S (LocalizedModule.mkLinearMap S M) hS, hn]
  let b := Module.finBasisOfFinrankEq (Localization S) (LocalizedModule S M) hrank
  obtain ⟨φ, hφ, hsurj⟩ := exists_map_of_basis S hS (LocalizedModule.mkLinearMap S M) b
  have hunit : ∀ s : S, ∃ k : ℕ, (s : 𝓞 E) = k ∧ ∃ u v : ℤ, u * k + v * N = 1 := by
    rintro ⟨_, k, -, hkc, rfl⟩
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hkc
    exact ⟨k, rfl, u, v, huv⟩
  refine ⟨φ, fun m => ?_, fun x c hxc => ?_⟩
  · obtain ⟨s, y, hs⟩ := hsurj m
    obtain ⟨k, hk, u, v, huv⟩ := hunit s
    rw [hk, Nat.cast_smul_eq_nsmul] at hs
    refine ⟨u • y, v • m, ?_⟩
    calc m = ((u * k + v * N : ℤ)) • m := by rw [huv, one_smul]
      _ = u • ((k : ℤ) • m) + (N : ℤ) • (v • m) := by
        rw [add_smul, mul_smul, mul_comm v, mul_smul]
      _ = φ (u • y) + N • (v • m) := by
        rw [map_zsmul, ← hs, natCast_zsmul, natCast_zsmul]
  · obtain ⟨s, y, hs⟩ := hsurj c
    obtain ⟨k, hk, u, v, huv⟩ := hunit s
    rw [hk, Nat.cast_smul_eq_nsmul] at hs
    have hNy : N • y = k • x := by
      apply hφ
      rw [map_nsmul, map_nsmul, ← hs, hxc, smul_comm]
    refine ⟨u • y + v • x, ?_⟩
    calc x = ((u * k + v * N : ℤ)) • x := by rw [huv, one_smul]
      _ = u • ((k : ℤ) • x) + v • ((N : ℤ) • x) := by
        rw [add_smul, mul_smul, mul_smul]
      _ = N • (u • y + v • x) := by
        rw [natCast_zsmul, natCast_zsmul, ← hNy, smul_add, smul_comm u N y, smul_comm v N x]

end GlobalTheory.CompanionTheory.ModFree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointLineBundleUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

open GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg

theorem valF_comp_valR {O C : Type} [CommRing O] [Field C] [Algebra O C] {X : Scheme.{0}} (a : Sp O ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ a ⁻¹ᵁ U) (f : Γ(X, U)) :
    valF (spMap (algebraMap O C) ≫ a) U f = algebraMap O C (valR a U h f) := by
  have h' : ⊤ ≤ (spMap (algebraMap O C) ≫ a) ⁻¹ᵁ U := fun x _ => h (x := spMap (algebraMap O C) x) trivial
  have e₀ : (spMap (algebraMap O C)).appLE ⊤ ⊤ (by first | exact le_rfl | simp) = (spMap (algebraMap O C)).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have e : (spMap (algebraMap O C) ≫ a).appLE U ⊤ h' = a.appLE U ⊤ h ≫ (spMap (algebraMap O C)).appTop := by
    rw [← e₀]
    exact (Scheme.Hom.appLE_comp_appLE (spMap (algebraMap O C)) a U ⊤ ⊤ h _).symm
  have n := congrArg (fun φ => φ.hom ((a.appLE U ⊤ h).hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap O C)))
  rw [valF, dite_eq_left h', e]
  exact n

theorem valR_unit {O : Type} [CommRing O] {X : Scheme.{0}} (a : Sp O ⟶ X) (U : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ U)
    (f : Γ(X, U)ˣ) : IsUnit (valR a U h f.val) :=
  f.isUnit.map (valR a U h)

theorem unit_alg {O : Type} [CommRing O] (t r0 r2 r1 : O) (u0 u1 u2 : Oˣ) (e0 : u0.val = r0) (e1 : u1.val = r1)
    (e2 : u2.val = r2) (M n : ℕ) :
    t ^ M * (u1 ^ n * ((u0 * u2 ^ M) ^ n)⁻¹ : Oˣ).val * (r0 * r2 ^ M) ^ n = t ^ M * r1 ^ n := by
  subst e0 e1 e2
  have : ((u1 ^ n * ((u0 * u2 ^ M) ^ n)⁻¹ * (u0 * u2 ^ M) ^ n : Oˣ)).val = (u1 ^ n : Oˣ).val := by
    rw [inv_mul_cancel_right]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at this ⊢
  rw [_root_.mul_assoc, this]

theorem torsVal_eq_unit_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (n : ℕ) (s : Out.H0 D.t.PP.L n) (O C : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field C] [Algebra O C] [FaithfulSMul O C] (ρ : 𝓞 L →+* O) (y : Over.mk (spMap ρ) ⟶ D.t.G) (N : ℕ), 1 ≤ N → y ^ N = 1 → ∀ (i : D.t.PP.L.ι) (h : ⊤ ≤ (show Sp O ⟶ D.t.G.left from y.left) ⁻¹ᵁ (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => (n : ℤ))).U (fun _ => i)) (b : Sp C ⟶ Sp (𝓞 L)), b = spMap (algebraMap O C) ≫ spMap ρ → ∀ (yC : Over.mk b ⟶ D.t.G), yC.left = spMap (algebraMap O C) ≫ y.left → ∀ T : C, TorsVal D.t.PP s yC N T → ∃ ε : Oˣ, T = algebraMap O C (valR (show Sp O ⟶ D.t.G.left from y.left) _ h (s.f fun _ => i) ^ (N ^ 2) * ε) := by
  intro E _ _ _ H L _ _ D n s O C _ _ _ _ _ _ ρ y N hN hy i h b hb yC hyC T hT
  subst hb
  obtain ⟨-, hyCN, w, -, -, hw, -, -, -⟩ := id hT
  let e : Sp O ⟶ D.t.G.left := (1 : Over.mk (spMap ρ) ⟶ D.t.G).left
  obtain ⟨i₀, h₀⟩ := exists_chart D.t.PP.isLB (e (IsLocalRing.closedPoint O))
  have he : ⊤ ≤ e ⁻¹ᵁ D.t.PP.L.U i₀ := top_le_of_closedPoint _ h₀
  have eN : (show Sp O ⟶ D.t.G.left from y.left) ≫ ((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left = e := by
    show y.left ≫ _ = _
    rw [left_pow, hy]
  have e1 : e ≫ ((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left = e := by
    show (1 : Over.mk (spMap ρ) ⟶ D.t.G).left ≫ _ = _
    rw [left_pow, one_pow]
  have hrig : spMap ρ ≫ eSec D.t.G = e := (one_left (Over.mk (spMap ρ))).symm
  have hi : ⊤ ≤ (show Sp O ⟶ D.t.G.left from y.left) ⁻¹ᵁ D.t.PP.L.U i := fun x _ =>
    Set.mem_iInter.1 (h (x := x) trivial) 0
  have hY : ⊤ ≤ (show Sp O ⟶ D.t.G.left from y.left) ⁻¹ᵁ
      LB.wchart D.t.PP.L (![((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left, 𝟙 D.t.G.left] : Fin 2 → _) ![i₀, i] := by
    intro x _
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · show (((show Sp O ⟶ D.t.G.left from y.left) ≫ ((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left) x) ∈ D.t.PP.L.U i₀
      rw [eN]; exact he (x := x) trivial
    · exact hi (x := x) trivial
  have hZ : ⊤ ≤ e ⁻¹ᵁ
      LB.wchart D.t.PP.L (![((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left, 𝟙 D.t.G.left] : Fin 2 → _) ![i₀, i₀] := by
    intro x _
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · show ((e ≫ ((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left) x) ∈ D.t.PP.L.U i₀
      rw [e1]; exact he (x := x) trivial
    · exact he (x := x) trivial
  have hR : ⊤ ≤ (show Sp O ⟶ (𝟙_ (Over (Sp (𝓞 L)))).left from spMap ρ) ⁻¹ᵁ
      LB.wchart D.t.PP.L (K := PUnit) (fun _ => eSec D.t.G) (fun _ => i₀) := by
    intro x _
    refine Set.mem_iInter.2 fun _ => ?_
    show (spMap ρ ≫ eSec D.t.G) x ∈ D.t.PP.L.U i₀
    rw [hrig]; exact he (x := x) trivial
  obtain ⟨u1, e1'⟩ := valR_unit _ _ hY (w.s ![i₀, i])
  obtain ⟨u0, e0'⟩ := valR_unit _ _ hZ (w.s ![i₀, i₀])
  obtain ⟨u2, e2'⟩ := valR_unit (X := (𝟙_ (Over (Sp (𝓞 L)))).left) _ _ hR (D.t.PP.rig.s fun _ => i₀)
  have hone : (1 : Over.mk (spMap (algebraMap O C) ≫ spMap ρ) ⟶ D.t.G).left = spMap (algebraMap O C) ≫ e := by
    show _ = spMap (algebraMap O C) ≫ (1 : Over.mk (spMap ρ) ⟶ D.t.G).left
    rw [one_left, one_left]
    simp
  refine ⟨u1 ^ n * ((u0 * u2 ^ (N ^ 2)) ^ n)⁻¹, ?_⟩
  have hT' : TorsVal D.t.PP s yC N (algebraMap O C (valR (show Sp O ⟶ D.t.G.left from y.left) _ h (s.f fun _ => i) ^ (N ^ 2) *
      (u1 ^ n * ((u0 * u2 ^ (N ^ 2)) ^ n)⁻¹ : Oˣ).val)) := by
    refine ⟨hN, hyCN, w, i₀, i, hw, ?_, ?_, ?_⟩
    · rw [hone]
      exact fun x _ => he (x := spMap (algebraMap O C) x) trivial
    · rw [hyC]
      exact fun x _ => hi (x := spMap (algebraMap O C) x) trivial
    · rw [hone, hyC]
      erw [valF_comp_valR e _ hZ, valF_comp_valR (X := (𝟙_ (Over (Sp (𝓞 L)))).left) _ _ hR,
        valF_comp_valR _ _ h, valF_comp_valR _ _ hY]
      have key := congrArg (algebraMap O C) (unit_alg (valR (show Sp O ⟶ D.t.G.left from y.left) _ h (s.f fun _ => i)) _ _ _
        u0 u1 u2 e0' e1' e2' (N ^ 2) n)
      simp only [map_mul, map_pow] at key ⊢
      exact key
  exact (_root_.GlobalTheory.CompanionTheory.Ar.Sl.TorsExist.torsVal_existsUnique E H L D n s C _ yC N hN hyCN).1.unique hT hT'

end GlobalTheory.CompanionTheory.Ar.Sl.Reg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitsMulRelationRearrangeCommRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

theorem units_mul_relation_rearrange_commRing {Q : Type} [CommRing Q] (D F V : Q) (h : D * D = 0) :
    (1 + D * F) * (1 + D * (V - F)) = 1 + D * V := by
  linear_combination (F * (V - F)) * h


set_option maxHeartbeats 4000000 in
theorem pfold : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (gs : Germ.PS k 2 d), AxOne gs → pow1 g.B p = Germ.ev (n := 2) ![ptPow k d p 0, Germ.pt k d 1] gs → ∀ y : Tm x p ⟶ t.G, y = homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p → homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → y ^ p = 1 → ∃ C : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] ![(p : ℤ), -(p : ℤ)]), C.IsGen ∧ (∀ (j : t.PP.L.ι) (h : pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j ≤ secZ t.G x p ⁻¹ᵁ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j)), ((secZ t.G x p).appLE _ _ h).hom (C.s fun _ => j).val = 1) ∧ ∀ j₀ : t.PP.L.ι, ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ → ∀ m : ℕ, ∃ v : Jet k (Fin 1 × Fin d) m, ∀ h : ⊤ ≤ rQ t.G x p (g.x m) ⁻¹ᵁ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j₀), ((rQ t.G x p (g.x m)).appLE _ ⊤ h).hom (C.s fun _ => j₀).val = toΓ _ (1 + dQ _ p ^ p * algebraMap _ _ (v ^ p - psJet m (dSer gs fun i => w i ^ p))) := by
  intro E _ _ _ H _ hstar X0 t k _ p _ _ x d g w gs hax hpow y hy hy0 hyp
  obtain ⟨κ, hκ, hκ2, hκ3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Nfold.nfold_first_law E H hstar X0 t p
  have hy1 : spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ y.left =
      spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ (1 : Tm x p ⟶ t.G).left := by
    have e₁ := congrArg (fun q => q.left) hy0
    have e₂ : homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ (1 : Tm x p ⟶ t.G) = 1 := by simp [Hom.one_def]
    exact e₁.trans (congrArg (fun q => q.left) e₂).symm
  obtain ⟨τ, hτ, hτ1⟩ := GlobalTheory.T.line_bundle_section_difference_generator t.G.left t.PP.L t.PP.isLB k p y.left (1 : Tm x p ⟶ t.G).left hy1
  obtain ⟨C, hC, hCv⟩ := GlobalTheory.T.frobenius_torsion_generator_relation E H X0 t k x p y hyp κ hκ τ hτ
  refine ⟨C, hC, GlobalTheory.T.frobenius_generator_correspondence E H X0 t k x p y hy0 κ hκ2 τ hτ1 C hCv, fun j₀ hj₀ m => ?_⟩
  obtain ⟨u, hu, hκ3'⟩ := hκ3 k x d g (p + m + 1)
  obtain ⟨e₀, he₀, hve⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Coc.Pf.frame_test_unit E H X0 t k p x d g w m j₀ hj₀
  obtain ⟨τ₀, hτ₀, hvτ⟩ := GlobalTheory.T.jet_section_generator_value E H X0 t k x p y (Jet k (Fin 1 × Fin d) m) hy0 τ hτ1 j₀ hj₀
  have hp0 : ((p : ℕ) : Jet k (Fin 1 × Fin d) m) = 0 := by
    have : ((p : ℕ) : k) = 0 := CharP.cast_eq_zero k p
    rw [← map_natCast (algebraMap k (Jet k (Fin 1 × Fin d) m)), this, map_zero]
  obtain ⟨v, hv⟩ := GlobalTheory.T.jet_augmentation_one_pth_power (Jet k (Fin 1 × Fin d) m) p hp0 ((e₀ * τ₀ : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ) : Jet (Jet k (Fin 1 × Fin d) m) Unit p) (by
    rw [Units.val_mul, map_mul, he₀, hτ₀, _root_.one_mul])
  refine ⟨v, fun h => ?_⟩
  have hju : jq w p m (u : Jet k (Fin 2 × Fin d) (p + m + 1)) = 1 + dQ _ p ^ p * algebraMap _ _ (psJet m (dSer gs fun i => w i ^ p)) := by
    rw [hu, hpow]
    exact GlobalTheory.T.germ_jet_quotient_formula k p d m w gs hax
  let f : Jet k (Fin 2 × Fin d) (p + m + 1) →+* Jet (Jet k (Fin 1 × Fin d) m) Unit p := (jq w p m : Jet k (Fin 2 × Fin d) (p + m + 1) →ₐ[k] _)
  let ν : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ := Units.map (f : _ →* Jet (Jet k (Fin 1 × Fin d) m) Unit p) u
  let U : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ := ν⁻¹ * (e₀ * τ₀) ^ p
  have hU : (U : Jet (Jet k (Fin 1 × Fin d) m) Unit p) = 1 + dQ _ p ^ p * algebraMap _ _ (v ^ p - psJet m (dSer gs fun i => w i ^ p)) := by
    have h2p : dQ (Jet k (Fin 1 × Fin d) m) p ^ p * dQ (Jet k (Fin 1 × Fin d) m) p ^ p = 0 := by
      rw [← pow_add]
      exact pow_eq_zero_of_le (by have := (Fact.out : p.Prime).one_lt; omega) (dQ_pow _ p)
    have e := units_mul_relation_rearrange_commRing (dQ (Jet k (Fin 1 × Fin d) m) p ^ p) (algebraMap _ _ (psJet m (dSer gs fun i => w i ^ p))) (algebraMap _ _ (v ^ p)) h2p
    rw [← hju, ← hv, ← RingHom.map_sub (algebraMap (Jet k (Fin 1 × Fin d) m) (Jet (Jet k (Fin 1 × Fin d) m) Unit p))] at e
    show ((ν⁻¹ * (e₀ * τ₀) ^ p : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ) : Jet (Jet k (Fin 1 × Fin d) m) Unit p) = _
    rw [Units.val_mul, Units.val_pow_eq_pow_val, ← e]
    exact Units.inv_mul_cancel_left ν _
  have hval : ∀ (z : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p))
      (J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
      (∀ ψ : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀) →
      val C (rQ t.G x p (g.x m)) z J = gm (𝟙 _) z ⊤ (unitΓ U) := by
    intro z J hJ hJ₀
    have hk : val κ (rQ t.G x p (g.x m) ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J =
        gm (𝟙 _) z ⊤ (unitΓ ν) * (gm (𝟙 _) z ⊤ (unitΓ e₀) ^ p)⁻¹ := by
      have e₁ : val κ (rQ t.G x p (g.x m) ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J =
          val (LB.pullGen t.PP.L _ _ κ (lift (jptG t x d g.x (p + m + 1) (0 : Fin 2)) (jptG t x d g.x (p + m + 1) (1 : Fin 2))).left) (homAt x (jq w p m)).left z J := by
        rw [_root_.GlobalTheory.CompanionTheory.Ar.Coc.TestPair.main E H X0 t k p x d g w m y hy]
        exact (val_pull hJ _ _ _).symm
      refine e₁.trans ((val_corr hJ hκ3' _).trans ((Pf.val_scale t _ _ _ _ _ z hJ).trans ?_))
      refine (congrArg (gm (spMap f) z ⊤ (unitΓ u) * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (_root_.GlobalTheory.CompanionTheory.Ar.Coc.Pf.peG_act_one E H hstar X0 t k p x d g w m (hy ▸ hyp) z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹)
          ((Pf.val_genPow t _ _ _ p _ z J).trans (congrArg (· ^ p) (hve z J hJ hJ₀)))))))).trans ?_
      rw [_root_.one_mul]
      exact congrArg (· * _) (Pf.gm_spMap f u z)
    have ht : val τ (rQ t.G x p (g.x m) ≫ (fst (Tm x p) t.G).left) z J = gm (𝟙 _) z ⊤ (unitΓ τ₀) := by
      rw [rQ_fst]
      exact hvτ z J hJ hJ₀
    rw [hCv _ _ z J hJ, hk, ht]
    let Φ : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ →* ((Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p)).presheaf.stalk z)ˣ :=
      (gm (𝟙 _) z ⊤).comp (Units.map (toΓ _).toMonoidHom)
    show (Φ ν * (Φ e₀ ^ p)⁻¹)⁻¹ * Φ τ₀ ^ p = Φ (ν⁻¹ * (e₀ * τ₀) ^ p)
    rw [map_mul Φ, map_inv Φ, map_pow Φ, map_mul Φ, mul_pow, mul_inv, inv_inv, _root_.mul_assoc]
  apply fn_ext
  intro z _
  have hz : rQ t.G x p (g.x m) z ∈ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j₀) := h trivial
  classical
  choose c hc using fun χ : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left => exists_chart t.PP.isLB (χ z)
  let J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι := fun ψ => if ψ z ∈ t.PP.L.U j₀ then j₀ else c ψ
  have hJ₀ : ∀ ψ : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀ := fun ψ e => if_pos e
  have hJ : Good t.PP.L z J := fun ψ => by
    by_cases e : ψ z ∈ t.PP.L.U j₀
    · rw [hJ₀ ψ e]; exact e
    · show ψ z ∈ t.PP.L.U (if ψ z ∈ t.PP.L.U j₀ then j₀ else c ψ)
      rw [if_neg e]; exact hc ψ
  have e := val_of C (rQ t.G x p (g.x m)) z J (fun _ => j₀) (fun i => hJ₀ _ (Set.mem_iInter.1 hz i))
  refine (Pf.gs_appLE _ _ _ h z trivial _).trans ((gs_unit _ z _ hz _).trans ?_)
  refine (congrArg Units.val (e.symm.trans (hval z J hJ hJ₀))).trans ?_
  rw [← hU]
  exact (gs_unit (𝟙 _) z ⊤ trivial (unitΓ U)).symm

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

