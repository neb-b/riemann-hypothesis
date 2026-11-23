module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2327
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationAdjointEndomorphismsCommute
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2483
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2482
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2735
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorProperties
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.Base

variable {p : ℕ} [Fact p.Prime] {P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop}
  (B : GlobalTheory.Dieu.Base p P)
  {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem map_id' {G : PDivGroup p k} (hG : P k G) : B.map hG hG (𝟙 G) = LinearMap.id :=
  LinearMap.ext fun m => B.smap_id G hG m

theorem map_comp' {G H K : PDivGroup p k} (hG : P k G) (hH : P k H) (hK : P k K) (f : G ⟶ H) (g : H ⟶ K) :
    B.map hG hK (f ≫ g) = B.map hG hH f ∘ₗ B.map hH hK g :=
  LinearMap.ext fun m => B.smap_comp hG hH hK (SemiHom.ofHom g) (SemiHom.ofHom f) (SemiHom.ofHom (f ≫ g))
    (fun _ _ => rfl) m

theorem map_add' {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (f g : G ⟶ H) :
    B.map hG hH (f + g) = B.map hG hH f + B.map hG hH g :=
  LinearMap.ext fun m => B.smap_add hG hH f g m

def mapAdd {G H : PDivGroup p k} (hG : P k G) (hH : P k H) :
    (G ⟶ H) →+ (B.M H hH →ₗ[WittVector p k] B.M G hG) :=
  AddMonoidHom.mk' (B.map hG hH) (B.map_add' hG hH)

theorem map_zero' {G H : PDivGroup p k} (hG : P k G) (hH : P k H) : B.map hG hH (0 : G ⟶ H) = 0 :=
  map_zero (B.mapAdd hG hH)

theorem map_pow_smul {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (n : ℕ) (f : G ⟶ H) (m : B.M H hH) :
    B.map hG hH ((p : ℤ_[p]) ^ n • f) m = p ^ n • B.map hG hH f m := by
  have e : (p : ℤ_[p]) ^ n • f = (p ^ n) • f := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have e2 : B.map hG hH ((p ^ n) • f) = (p ^ n) • B.map hG hH f := map_nsmul (B.mapAdd hG hH) _ _
  rw [e, e2, LinearMap.smul_apply]

theorem red_map {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (f : G ⟶ H) (m : B.M H hH) :
    B.red G hG (B.map hG hH f m) = rigExtMap f (B.red H hH m) := by
  have := B.red_smap hG hH (SemiHom.ofHom f) m
  rw [SemiHom.ofHom_rig] at this
  exact this

theorem map_F {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (f : G ⟶ H) (m : B.M H hH) :
    B.map hG hH f (B.F H hH m) = B.F G hG (B.map hG hH f m) := by
  let u := (SemiHom.ofHom f).comp (absFrob (p_eq_zero p k) H)
  have e1 : B.smap hG hH u m = B.map hG hH f (B.F H hH m) :=
    B.smap_comp hG hH hH (absFrob (p_eq_zero p k) H) (SemiHom.ofHom f) u (fun _ _ => rfl) m
  have e2 : B.smap hG hH u m = B.F G hG (B.map hG hH f m) :=
    B.smap_comp hG hG hH (SemiHom.ofHom f) (absFrob (p_eq_zero p k) G) u
      (fun n a => by simp only [u, SemiHom.comp_app, SemiHom.ofHom_app, absFrob_app, map_pow]) m
  exact e1.symm.trans e2

theorem finrank_M (G : PDivGroup p k) (hG : P k G) :
    Module.finrank (WittVector p k) (B.M G hG) = G.height := by
  haveI := B.free G hG
  haveI := B.finite G hG
  obtain ⟨_, h5⟩ := finrank_eq_of_semilinear_surjective (WittVector.constantCoeff_surjective p)
    (p_eq_zero p k) (B.red G hG) (B.red_surjective G hG) fun m => (B.red_eq_zero G hG m).1
  exact h5.symm.trans (_root_.GlobalTheory.PDivGroup.finrank_rigExt_omega p k (p_eq_zero p k) G).2.2.1

theorem eq_zero_of_pow_smul {G : PDivGroup p k} (hG : P k G) (n : ℕ) (m : B.M G hG) (h : p ^ n • m = 0) :
    m = 0 := by
  haveI := B.free G hG
  rw [← Nat.cast_smul_eq_nsmul (WittVector p k)] at h
  refine (smul_eq_zero.1 h).resolve_left ?_
  rw [Nat.cast_pow]
  exact pow_ne_zero _ (WittVector.p_ne_zero p k)

end GlobalTheory.Dieu.Base

namespace GlobalTheory.Dieu

theorem base_functor_props : ∀ (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop) (B : Base p P) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H K : PDivGroup p k) (hG : P k G) (hH : P k H) (hK : P k K), B.map hG hG (𝟙 G) = LinearMap.id ∧ (∀ (f : G ⟶ H) (g : H ⟶ K), B.map hG hK (f ≫ g) = B.map hG hH f ∘ₗ B.map hH hK g) ∧ (∀ f g : G ⟶ H, B.map hG hH (f + g) = B.map hG hH f + B.map hG hH g) ∧ B.map hG hH (0 : G ⟶ H) = 0 ∧ (∀ (n : ℕ) (f : G ⟶ H) (m : B.M H hH), B.map hG hH ((p : ℤ_[p]) ^ n • f) m = p ^ n • B.map hG hH f m) ∧ (∀ (f : G ⟶ H) (m : B.M H hH), B.red G hG (B.map hG hH f m) = rigExtMap f (B.red H hH m)) ∧ (∀ (f : G ⟶ H) (m : B.M H hH), B.map hG hH f (B.F H hH m) = B.F G hG (B.map hG hH f m)) ∧ Module.finrank (WittVector p k) (B.M G hG) = G.height ∧ ∀ (n : ℕ) (m : B.M G hG), p ^ n • m = 0 → m = 0 := by
  intro p _ P B k _ _ _ G H K hG hH hK
  exact ⟨B.map_id' hG, fun f g => B.map_comp' hG hH hK f g, B.map_add' hG hH, B.map_zero' hG hH,
    B.map_pow_smul hG hH, B.red_map hG hH, B.map_F hG hH, B.finrank_M G hG, B.eq_zero_of_pow_smul hG⟩

end GlobalTheory.Dieu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.GSetup

open GlobalTheory.ThetaSysOfObj

theorem exists_big_ge (g n : ℕ) (hn : 2 ≤ n) (B : ℕ) : ∃ k j₁ : ℕ, 2 ≤ k ∧ B ≤ (n ^ k) ^ 2 ∧ 1 ≤ j₁ ∧ ∀ j ≥ j₁,
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω),
      S.g = g → S.N = (n ^ k) ^ 2 → S.r = n ^ j → S.Big := by
  have lt : ∀ m : ℕ, m < n ^ m := fun m => Nat.lt_pow_self hn
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2))
  set K := max k₀ B with hK
  set N := (n ^ (K + 2)) ^ 2 with hN
  have hN₁ : K + 2 < N := (lt _).trans_le (Nat.le_self_pow two_ne_zero _)
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt
    (2 * ((N ^ g * g.factorial : ℕ) : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)))
  refine ⟨K + 2, j₀ + 6 * (N ^ g * g.factorial) + 1, by omega, ?_, by omega, fun j hj o Ω _ _ _ S hg hS hr => ?_⟩
  · have : B ≤ K := le_max_right _ _
    omega
  have hj' := lt j
  unfold ThetaSys.Big
  rw [hg, hS, hr, ← hN]
  have hk₀K : k₀ ≤ K := le_max_left _ _
  refine ⟨hk₀.trans (by exact_mod_cast (by omega : k₀ < N)), ?_, ?_⟩
  · rw [Nat.cast_mul (n ^ j)]
    exact mul_lt_mul_of_pos_right (hj₀.trans (by exact_mod_cast (by omega : j₀ < n ^ j)))
      (by exact_mod_cast (by omega : 0 < N))
  · exact lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right _ (by omega))

theorem exists_big_thetaSys_ge : ∀ (ℓ g : ℕ), ℓ.Prime → Odd ℓ → ∀ B : ℕ, ∃ k j₀ : ℕ, B ≤ (ℓ ^ k) ^ 2 ∧ ∀ j ≥ j₀, ∀ (o Ω : Type) [CommRing o]
    [Field Ω] [Algebra o Ω] [ArithBase o Ω] (R : Subalgebra o Ω) (J : Type) (b : TBase o ((ℓ ^ j) ^ 2))
    (u : TObj g ((ℓ ^ j) ^ 2) J b (spMap (algebraMap o R))) (w w' : J), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) →
    u.Prim w w' → ∃ (S : ThetaSys o Ω) (ρ : S.Real) (hR : R ≤ S.R) (φ : ρ.P.A.left ⟶ u.A.left), S.Big ∧
      S.N = (ℓ ^ k) ^ 2 ∧ IsGrpPullback ρ.P.A u.A (spMap (Subalgebra.inclusion hR).toRingHom) φ ∧ LBIso ρ.P.L (u.L.pull φ) := by
  intro n g hn ho B
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨k, j₁, hk, hBk, hj₁, big⟩ := exists_big_ge g n hn.two_le B
  refine ⟨k, j₁ + 2 * k, hBk, fun j hj => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + k * 2 := ⟨j - k * 2, by omega⟩
  rw [pow_add, pow_mul]
  intro o Ω _ _ _ hb R J b u w₁ w₂ hR hΩ hpr
  have := u.ab.comm
  have : NeZero ((n ^ j * (n ^ k) ^ 2) ^ 2) := ⟨by have := hn.pos; positivity⟩
  have hS : ZH.HypS u.A u.L := ⟨u.act w₁, u.act w₂, u.hom w₁, u.hom w₂, hpr.1, hpr.2.2, hpr.2.1⟩
  have hun : IsUnit (n : o) := isUnit_of_dvd_unit (Nat.cast_dvd_cast
    (((dvd_pow_self n (by omega : j ≠ 0)).trans (dvd_mul_right _ _)).trans (dvd_pow_self _ two_ne_zero))) b.unit
  obtain ⟨lev, -⟩ := exists_level R u
  obtain ⟨S, ρ, h, φ, -, hN, hr, hg, hp, hlb, -⟩ :=
    GlobalTheory.ThetaReal.exists_thetaSys_real hL hL₂ o Ω R hR hΩ u.pol n k j b.ζ hn ho hk (by omega) hun hS lev
  exact ⟨S, ρ, h, φ, big j (by omega) o Ω S hg hN hr, hN, hp, hlb⟩

theorem exists_thetaSys_at : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ),
    IsE8 W → ∀ η ∈ genericPoints F.X, ∀ B : ℕ, ∃ (o₁ Ω₁ : Type) (_ : CommRing o₁) (_ : Field Ω₁) (_ : Algebra o₁ Ω₁)
      (_ : ArithBase o₁ Ω₁) (κ : cycAway n →+* o₁) (S : ThetaSys o₁ Ω₁) (ρ : S.Real) (u : Sp S.R ⟶ F.X),
      S.Big ∧ B ≤ S.N ∧ SharpOver F W ρ.P u ∧ (∀ w, (spMap S.R.val.toRingHom ≫ u) w = η) ∧
      spMap S.R.val.toRingHom ≫ u ≫ F.s = spMap ((algebraMap o₁ Ω₁).comp κ) ∧ κ.Finite ∧
      ((spMap S.R.val.toRingHom ≫ u).stalkMap (genericPoint (Sp Ω₁))).hom.Finite := by
  intro g n hg hn ho F W hW η hη B
  obtain ⟨ℓ, hℓ, hℓo, H⟩ := _root_.GlobalTheory.PoincChart.exists_chart g n hg hn ho F W hW η hη
  obtain ⟨k, j₀, hBk, Hs⟩ := exists_big_thetaSys_ge ℓ (8 * g) hℓ hℓo B
  obtain ⟨o, Ω, i₁, i₂, i₃, i₄, κ, R, J, b, t, w, w', x, hfg, hfr, hprim, hsh, hηx, hbase, hκ, hst⟩ :=
    H (max j₀ 1) (le_max_right _ _)
  obtain ⟨S, ρ, hR, φ, hbig, hN, hpb, hL⟩ := Hs (max j₀ 1) (le_max_left _ _) o Ω R J b t w w' hfg hfr hprim
  have ef : spMap S.R.val.toRingHom ≫ spMap (Subalgebra.inclusion hR).toRingHom = spMap R.val.toRingHom :=
    (Spec.map_comp (CommRingCat.ofHom (Subalgebra.inclusion hR).toRingHom) (CommRingCat.ofHom S.R.val.toRingHom)).symm
  refine ⟨o, Ω, i₁, i₂, i₃, i₄, κ, S, ρ, spMap (Subalgebra.inclusion hR).toRingHom ≫ x, hbig, hN ▸ hBk,
    hsh _ _ ρ.P φ hpb hL, ?_, ?_, hκ, ?_⟩
  · intro w
    rw [← Category.assoc, ef]
    exact hηx w
  · rw [Category.assoc, ← Category.assoc (spMap S.R.val.toRingHom), ef]
    exact hbase
  · rw [← Category.assoc, ef]
    exact hst

theorem exists_setup : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n))
    (i : F.X ⟶ Z), IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → IsOpenImmersion i → i ≫ z = F.s →
    Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i →
    ∀ η ∈ genericPoints F.X, ∀ B : ℕ, ∃ X₁ : Setup F W i, B ≤ X₁.S.N ∧ ∀ w, (spMap X₁.S.R.val.toRingHom ≫ X₁.u) w = η := by
  intro g n hg hn ho F Z z i hproj hZn hopen hiz hden W hW hT η hη B
  obtain ⟨o₁, Ω₁, _, _, _, _, κ, S, ρ, u, hbig, hB, hsharp, hgen, hbase, hκ, hstalk⟩ :=
    exists_thetaSys_at g n hg hn ho F W hW η hη B
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _
  haveI : IsProper z := ((isProjOver_iff_isProper_and_exists_isAmpleLB z).1 hproj).1
  have hp : (spMap S.R.val.toRingHom ≫ u ≫ i) ≫ z = spMap ((algebraMap o₁ Ω₁).comp κ) := by
    simp only [Category.assoc, hiz]
    simpa only [Category.assoc] using hbase
  have hst : ((spMap S.R.val.toRingHom ≫ u ≫ i).stalkMap (genericPoint (Sp Ω₁))).hom.Finite := by
    rw [← Category.assoc, Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp hstalk (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (i.stalkMap _)).2)
  obtain ⟨M, π, hMn, hπ, hcomp⟩ := _root_.GlobalTheory.Poinc.exists_ratModel_normalization (cycAway n) o₁ Ω₁ κ hκ Z z inferInstance inferInstance inferInstance
    (spMap S.R.val.toRingHom ≫ u ≫ i) hp hst
  exact ⟨Setup.mk o₁ Ω₁ S ρ hbig u hsharp (fun w => (hgen w).symm ▸ hη) M (GlobalTheory.IsNormalScheme.of_pred hMn) π hπ hcomp
    hg hn ho z hproj (GlobalTheory.IsNormalScheme.of_pred hZn) hopen hiz hden hW hT κ hbase, hB, hgen⟩

end GlobalTheory.Poinc.GSetup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqCounitOfHeightOneCotangentPullbackZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.HeightOneHom

theorem primitive_apply_mul {k C : Type} [Field k] [CommRing C] [HopfAlgebra k C]
    [IsCocomm k C] [Module.Finite k C] {φ : CartierDual k C} (hφ : cobOne k (CartierDual k C) φ = 0) (a b : C) :
    φ.ofConv (a * b) = counitAlgHom k C a • φ.ofConv b + counitAlgHom k C b • φ.ofConv a := by
  rw [cobOne_apply, sub_sub, sub_eq_zero, CartierDual.comul_eq_iff] at hφ
  have h := hφ a b
  rw [map_add (f := _), LinearMap.add_apply, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul,
    CartierDual.one_apply, CartierDual.one_apply] at h
  change φ (a * b) = _
  rw [← h]
  simp only [counitAlgHom_apply, smul_eq_mul]
  ring

theorem eq_algebraMap_counit_of_cotMap_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C]
    (D : Type) [CommRing D] [HopfAlgebra k D] [IsCocomm k D] [Module.Finite k D]
    (f : D →ₐc[k] C), (∀ a ∈ augIdeal k C, a ^ p = 0) → cotMap f = 0 →
    ∀ d, f d = algebraMap k C (counit (R := k) d) := by
  intro p _ k _ _ C _ _ _ _ D _ _ _ _ f hpow hcot d
  have hgen := GlobalTheory.HeightOneDual.adjoin_primitive_eq_top p k C hpow
  have hzero : ∀ φ : CartierDual k C, cobOne k (CartierDual k C) φ = 0 → ∀ x, φ (f x) = 0 := by
    intro φ hφ x
    have h1 := AugCot.lift_d (counitAlgHom k C) φ.ofConv (primitive_apply_mul hφ) (f x)
    have h2 : dUnit (R := k) (f x) = 0 := by
      rw [← cotMap_d f x, hcot, LinearMap.zero_apply]
    change φ.ofConv (f x) = 0
    rw [← h1]
    change AugCot.lift (counitAlgHom k C) φ.ofConv (primitive_apply_mul hφ) (dUnit (R := k) (f x)) = 0
    rw [h2, map_zero]
  have hone : ∀ φ : CartierDual k C, cobOne k (CartierDual k C) φ = 0 → φ 1 = 0 := by
    intro φ hφ
    have := AugCot.pointDer_algebraMap (primitive_apply_mul hφ) (1 : k)
    rwa [map_one] at this
  let T : CartierDual k C →ₐ[k] CartierDual k D :=
    (Algebra.ofId k _).comp (counitAlgHom k (CartierDual k C))
  have hT : ∀ φ : CartierDual k C, ∀ x : D, T φ x = φ 1 * counit (R := k) x := by
    intro φ x
    change (algebraMap k (CartierDual k D) (counit (R := k) φ)) x = _
    rw [Algebra.algebraMap_eq_smul_one, CartierDual.counit_apply]
    change φ 1 • (1 : CartierDual k D) x = _
    rw [CartierDual.one_apply, smul_eq_mul]
  have hM : (CartierDual.map f : CartierDual k C →ₐ[k] CartierDual k D) = T := by
    refine AlgHom.ext_of_adjoin_eq_top hgen fun φ hφ => ?_
    refine CartierDual.ext_apply fun x => ?_
    change CartierDual.map f φ x = T φ x
    rw [CartierDual.map_apply, hT, hzero φ hφ x, hone φ hφ, zero_mul]
  refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
  have h1 : CartierDual.map f φ d = T φ d := by
    rw [← hM]; rfl
  rw [CartierDual.map_apply, hT] at h1
  rw [h1, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.HeightOneHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFormalGroupLawCoboundaryOneEqZero
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem eq_zero_of_cob1_eq_zero : ∀ (p : ℕ) (k : Type) [CommRing k] (h : (p : k) = 0) (d : ℕ)
    (G : PDivGroup p k) (c : Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k),
    c.IsLawOf μ → ∀ b, cob1 μ b = 0 → b = 0 := by
  intro p k _ h d G c μ hμ b hb
  obtain ⟨hres, -, huniq⟩ := _root_.GlobalTheory.Katz.Chart.functions_are_series p k d G c
  have hlaw := ((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).2
  let B : G.funs := ⟨fun n => c.ev n b, fun n => hres n b⟩
  have hB : G.cob B = 0 := by
    refine Subtype.ext (funext fun n => ?_)
    change cobOne k (G.A n) (c.ev n b) = 0
    rw [← (hlaw n b).2, hb, map_zero]
  have hB0 := G.eq_zero_of_cob_eq_zero h hB
  have hb0 : ∀ n, c.ev n b = 0 := fun n => congrArg (fun B : G.funs => B.1 n) hB0
  obtain ⟨f, -, hf⟩ := huniq (fun _ => 0) (fun n => map_zero _)
  exact (hf b hb0).trans (hf 0 fun n => map_zero _).symm

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgClosedFieldTorsionMapsCommuteHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.Two

open GlobalTheory.Balanced

section Gen
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I}
  {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂]
  [IsCommMonObj G₂] {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂}

theorem toG_gen₀ {a : G₁ ⟶ G₂} {c : A₁.A ⟶ A₂.A} (hc : Gen₀ U₁ U₂ a c) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ A₁.A) : toG U₂ (x ≫ c) = toG U₁ x ≫ a.left := by
  have e : c ≫ U₂.gen.inv = U₁.gen.inv ≫ (Over.pullback (jK R)).map a := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e' : c.left ≫ U₂.gen.inv.left = U₁.gen.inv.left ≫ ((Over.pullback (jK R)).map a).left :=
    congrArg (fun q => q.left) e
  have e₂ : ((Over.pullback (jK R)).map a).left ≫ pullback.fst G₂.hom (jK R) = pullback.fst G₁.hom (jK R) ≫ a.left :=
    pullback.lift_fst _ _ _
  calc toG U₂ (x ≫ c) = x.left ≫ (c.left ≫ U₂.gen.inv.left) ≫ pullback.fst G₂.hom (jK R) := by
        simp only [toG, Over.comp_left, Category.assoc]
    _ = _ := by rw [e', Category.assoc, e₂, toG, Category.assoc, Category.assoc]

end Gen

theorem exists_toG_pull {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V}
    (φ : R →+* V) {D : DegData R I} {D' : DegData V I'} {A : PolAV (Sp (FractionRing R))}
    {A' : PolAV (Sp (FractionRing V))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (U' : UnifPre I' D' A' ((Over.pullback (specOf φ)).obj G))
    {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F]
    (hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) =
      algebraMap (FractionRing V) F (algebraMap V _ (φ r))) (z : TFK (R := R) F ⟶ A.A) :
    ∃ z' : TFK (R := V) F ⟶ A'.A, toG U' z' ≫ pullback.fst G.hom (specOf φ) = toG U z := by
  have w : toG U z ≫ G.hom = (jFK (R := V) F ≫ jK V) ≫ specOf φ := by
    rw [toG_over]
    simp only [jFK, jK, specOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hF
  obtain ⟨z', hz'⟩ := exists_toG U' (pullback.lift _ _ w) (pullback.lift_snd _ _ _)
  exact ⟨z', by rw [hz']; exact pullback.lift_fst _ _ _⟩


set_option maxHeartbeats 2000000 in
theorem exists_key : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → Function.Injective h → ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : Algebra (FractionRing R) F), Key U₁.toUnifPre U₂.toUnifPre c b h F := by
  intro R _ _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ hG₁ hG₂ U₁ U₂ a c b h _ hgen hlin hcoord hinj
  have hL := GlobalTheory.firstFiveLaws
  obtain ⟨V, _, _, _, φ, hV, hφ, hI⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.1 R I hR
  have : CharZero V := charZero_of_injective_ringHom hφ
  have hR' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨v, hv⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 V ϖ hϖ
  obtain ⟨D₁', hD₁, A₁', U₁', hG₁', hU₁, hpt₁, -⟩ := _root_.GlobalTheory.UT.EndBaseChange.main hL R I hR D₁ A₁ G₁ hG₁ U₁ V φ hV hφ hI
  obtain ⟨D₂', hD₂, A₂', U₂', hG₂', hU₂, hpt₂, -⟩ := _root_.GlobalTheory.UT.EndBaseChange.main hL R I hR D₂ A₂ G₂ hG₂ U₂ V φ hV hφ hI
  let Ω := AlgebraicClosure (FractionRing V)
  let ψ : R →+* Ω := ((algebraMap (FractionRing V) Ω).comp (algebraMap V (FractionRing V))).comp φ
  have hψ : Function.Injective ψ :=
    ((algebraMap (FractionRing V) Ω).injective.comp (IsFractionRing.injective V (FractionRing V))).comp hφ
  let _ : Algebra (FractionRing R) Ω := (IsFractionRing.lift hψ).toAlgebra
  have hF : ∀ r : R, algebraMap (FractionRing R) Ω (algebraMap R _ r) =
      algebraMap (FractionRing V) Ω (algebraMap V _ (φ r)) := fun r => IsFractionRing.lift_algebraMap hψ r
  obtain ⟨ex₁, -, io₁, ns₁⟩ := hpt₁ Ω hF
  obtain ⟨ex₂, sur₂, io₂, ns₂⟩ := hpt₂ Ω hF
  obtain ⟨b', h', hlin', hb', hh'⟩ := _root_.GlobalTheory.Mum.Two.PullLin.linPull R V I (maximalIdeal V) φ D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ D₁' D₂' A₁' A₂'
    hD₁ hD₂ U₁' U₂' hU₁ hU₂ a b h hlin
  have hcoord' := _root_.GlobalTheory.Mum.Two.coord_of_lin V (maximalIdeal V) hR' D₁' D₂' A₁' A₂' _ _ U₁'.toUnifPre U₂'.toUnifPre
    ((Over.pullback (specOf φ)).map a) b' h' hlin'
  let c' : A₁'.A ⟶ A₂'.A := U₁'.gen.inv ≫ (Over.pullback (jK V)).map ((Over.pullback (specOf φ)).map a) ≫ U₂'.gen.hom
  have hgen' : Gen₀ U₁'.toUnifPre U₂'.toUnifPre ((Over.pullback (specOf φ)).map a) c' := by
    simp only [Gen₀, c', Iso.hom_inv_id_assoc]
  have hc' : IsMonHom c' := by
    have := U₁'.gen_hom
    have := U₂'.gen_hom
    have := hlin'.1
    dsimp only [c']
    infer_instance
  have hinj' : Function.Injective h' := fun x y hxy => hD₂.xe.injective (hinj (by rw [← hh', ← hh', hxy]))
  have key' := _root_.GlobalTheory.Mum.Two.KeyDvr.main V hV ϖ hϖ Ω v hv D₁' D₂' A₁' A₂' _ _ hG₁' hG₂' U₁' U₂' ((Over.pullback (specOf φ)).map a)
    c' b' h' hc' hgen' hlin' hcoord' hinj'
  choose π₁ hπ₁ _ using ex₁
  choose π₂ hπ₂ _ using ex₂
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, fun k hk p x hx g' hact => ?_⟩
  have hact' : Act D₁'.toPre D₂'.toPre b' h' (π₁ p.g) (π₂ g') :=
    (_root_.GlobalTheory.Mum.Two.ActPull.main R V φ D₁.toPre D₂.toPre D₁'.toPre D₂'.toPre hD₁ hD₂ b h b' h' hlin.2.1 hlin'.2.1 hb' hh'
      (fun χ => (hcoord χ).imp fun _ hu => hu.1) Ω p.g g' (π₁ p.g) (π₂ g') (hπ₁ _) (hπ₂ _)).1 hact
  let ρp : QkPt D₁'.toPre Ω k := ⟨hD₁.xe.symm p.y, π₁ p.g, by
    obtain ⟨s, h1, h2⟩ := p.eq
    exact ⟨π₁ s, (ns₁ k _ _ _ _ (hπ₁ _) (hπ₁ _)).1 h1, (io₁ _ _ _ (hπ₁ _)).1 (by rwa [AddEquiv.apply_symm_apply])⟩⟩
  obtain ⟨x', hx'e⟩ := exists_toG_pull φ U₁.toUnifPre U₁'.toUnifPre hF x
  have hx' : QkToAkU U₁'.toUnifPre Ω k ρp x' :=
    hL.2.2.2.2.qkBaseChange R V I _ hR hR' φ D₁ A₁ G₁ U₁ _ (Iso.refl _) (inferInstanceAs (IsMonHom (𝟙 _))) A₁' D₁'
      hD₁ U₁' hU₁ Ω hF k hk p x ρp x' rfl (hπ₁ _)
      (by simpa only [toG, Category.assoc, Iso.refl_hom, Over.id_left, Category.id_comp] using hx'e) hx
  obtain ⟨r, rg, hr⟩ := key' k hk ρp x' hx' (π₂ g') hact'
  let p' : QkPt D₂.toPre Ω k := ⟨hD₂.xe r.y, g', by
    obtain ⟨s', h1, h2⟩ := r.eq
    obtain ⟨s, hs, -⟩ := sur₂ s'
    exact ⟨s, (ns₂ k _ _ _ _ (hπ₂ g') hs).2 (rg ▸ h1), (io₂ _ _ _ hs).2 h2⟩⟩
  refine ⟨p', rfl, ?_⟩
  obtain ⟨f₂, hf₂, -⟩ := _root_.GlobalTheory.TorsionIso.torsion_eq hL R I hR D₂ A₂ G₂ hG₂ U₂ Ω k hk
  obtain ⟨f₂', hf₂', -⟩ := _root_.GlobalTheory.TorsionIso.torsion_eq hL V _ hR' D₂' A₂' _ hG₂' U₂' Ω k hk
  obtain ⟨z', hz'e⟩ := exists_toG_pull φ U₂.toUnifPre U₂'.toUnifPre hF (f₂ p')
  have hz' : QkToAkU U₂'.toUnifPre Ω k r z' :=
    hL.2.2.2.2.qkBaseChange R V I _ hR hR' φ D₂ A₂ G₂ U₂ _ (Iso.refl _) (inferInstanceAs (IsMonHom (𝟙 _))) A₂' D₂'
      hD₂ U₂' hU₂ Ω hF k hk p' (f₂ p') r z' (hD₂.xe.symm_apply_apply r.y).symm (rg ▸ hπ₂ g')
      (by simpa only [toG, Category.assoc, Iso.refl_hom, Over.id_left, Category.id_comp] using hz'e) ((hf₂ _ _).2 rfl)
  have ez : z' = x' ≫ c' := ((hf₂' _ _).1 hz').trans ((hf₂' _ _).1 hr).symm
  have hpa : ((Over.pullback (specOf φ)).map a).left ≫ pullback.fst G₂.hom (specOf φ) =
      pullback.fst G₁.hom (specOf φ) ≫ a.left := pullback.lift_fst _ _ _
  refine (hf₂ _ _).2 (toG_injective U₂.toUnifPre ?_).symm
  rw [← hz'e, ez, toG_gen₀ hgen', toG_gen₀ hgen, ← hx'e, Category.assoc, Category.assoc, hpa]

end GlobalTheory.Mum.Two
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqvRational
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_eqv_rational : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E, Eqv D.toPre A (Kb R) N lab E → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, LabExt σ lab lab) → ∃ (Φ : IntFam (maximalIdeal R) D.toPre N → H0 A.L N) (E₀ : _), Eqv D.toPre A (Kb R) N lab E₀ ∧ ∀ F₀ s, F₀.Over s → Agree A.L (E₀ s) (Φ F₀) := by
  intro R _ _ _ hB D A N hN lab E hE hlab
  have hc0 : CharZero R := hB.2
  choose E' hE' hT using fun σ => GlobalTheory.T.exists_galoisConjugate_equivariantBijection_twist R hB D A N hN lab E hE hlab σ
  choose c hc using fun σ => _root_.GlobalTheory.Mum.eqv_eq_smul R (maximalIdeal R) D A (Kb R) N hN lab E (E' σ) hE (hE' σ)
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.T.exists_common_scaling_descends_to_fractionField R hB A N {q : IntFam (maximalIdeal R) D.toPre N × Fam D.toPre (Kb R) N // q.1.Over q.2}
    (fun i => E i.1.2) c (fun σ i => ⟨E' σ i.1.2, hT σ i.1.1 i.1.2 i.2, hc σ i.1.2⟩)
  obtain ⟨E₀, hE₀, hE₀f⟩ := _root_.GlobalTheory.Mum.ScaleEqv.eqv_scale R D.toPre A (Kb R) N lab E hE c₀
  choose Φ hΦ using hc₀
  have hex := fun F₀ => _root_.GlobalTheory.Mum.IntFam.existsUnique_over R (maximalIdeal R) D.toPre N F₀ (Kb R)
  refine ⟨fun F₀ => Φ ⟨(F₀, (hex F₀).exists.choose), (hex F₀).exists.choose_spec⟩, E₀, hE₀, fun F₀ s hs => ?_⟩
  obtain rfl : (hex F₀).exists.choose = s := (hex F₀).unique (hex F₀).exists.choose_spec hs
  exact hΦ _ (E₀ _) (hE₀f _)

end GlobalTheory.Mum
end

