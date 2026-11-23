module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfInvGenOfInvariants
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecOnNonvanishingOfTameQuotient
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ResidueFieldMapFiniteSeparableOfTame
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianDescentTameQuotient
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem fixes_iff_fixes_image {X Y T : Scheme.{0}} (p : Y ⟶ X) (r : X ⟶ X) (q : Y ⟶ Y) (y : T ⟶ Y)
    (w : q ≫ p = p ≫ r)
    (h : (y ≫ p) ≫ r = y ≫ p → pullback.fst p (y ≫ p) ≫ q = pullback.fst p (y ≫ p)) :
    y ≫ q = y ↔ (y ≫ p) ≫ r = y ≫ p := by
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [Category.assoc, ← w, ← Category.assoc, hy]
  · have := pullback.lift y (𝟙 _) (Category.id_comp _).symm ≫= h hy
    rwa [pullback.lift_fst_assoc, pullback.lift_fst] at this

theorem exists_sab_descent_of_tame_quotient :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (R : Type) [CommRing R] (X X' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (π : X ⟶ X') (t : SAB H X) (s : X ⟶ Sp R) (τ : Γ →* Aut t.G.left) (mu : ∀ g, SABMap t t (ρ g).asIso.hom), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsFinite π → IsQProjOver (t.G.hom ≫ s) → (IsReduced X ∧ genericPoints X ⊆ abLocus t.G) → (∀ g, (mu g).φ = (τ g).asIso.hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst t.G.hom x ≫ (τ g).asIso.hom = pullback.fst t.G.hom x) → ∃ (t' : SAB H X') (ν : SABMap t t' π), (∀ g, (τ g).asIso.hom ≫ ν.φ = ν.φ) ∧ (Good t → PushInvertible t.G t.PP.L → Good t') := by
  intro E _ _ _ H Γ _ _ R _ X X' _ ρ π t s τ mu hQ hfin hqp hga hmu htame hfib
  have hsemi := t.semi
  have hcart (g : Γ) : IsGrpPullback t.G t.G (ρ g).asIso.hom (τ g).asIso.hom := hmu g ▸ (mu g).cart
  have hw (g : Γ) : (τ g).asIso.hom ≫ t.G.hom = t.G.hom ≫ (ρ g).asIso.hom := (hcart g).1.w
  have hact (g : Γ) (c) : (t.act.act c).left ≫ (τ g).asIso.hom = (τ g).asIso.hom ≫ (t.act.act c).left :=
    hmu g ▸ (mu g).act c
  have he (g : Γ) : eSec t.G ≫ (τ g).asIso.hom = (ρ g).asIso.hom ≫ eSec t.G := by
    have := (mu g).cm.e_comm
    rw [(mu g).base] at this
    rw [← hmu g]
    exact this
  have hL (g : Γ) : LBIso t.PP.L (t.PP.L.pull (τ g).asIso.hom) := by
    obtain ⟨w, hw, -⟩ := (mu g).lin
    rw [← hmu g]
    exact ⟨w, hw⟩
  have hsec : eSec t.G ≫ t.G.hom = 𝟙 X := Over.w (η[t.G])
  have hgi : GeometricallyIntegral t.G.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hsemi.smooth hsemi.geomConnected
  obtain ⟨-, hsurj, -⟩ := quotient_isIntegral_surjective_orbits Γ X X' ρ π hQ
  obtain ⟨G', φ, hpb, hsm, hinv⟩ :=
    exists_smooth_descent_of_tame_quotient Γ R X X' ρ π t.G s τ hQ hfin hqp hsemi.smooth hw htame hfib
  obtain ⟨_, _, a', hgp, ha⟩ := quotient_descend_grpObj Γ (𝓞 E) X X' ρ π t.G G' φ τ t.act hQ hpb inferInstance
    fun g => ⟨hinv g, hcart g, hact g⟩
  have hsemi' := (SemiAbelianDescent.main X X' π t.G G' φ inferInstance hsurj hgp hsm hsemi).1
  obtain ⟨u, hu₁, hu₂, hu₃⟩ := RigidLinearisation.exists_linearisation Γ X t.G (eSec t.G) ρ τ t.PP.L hsec hgi
    (eq_one_of_appLE_section_eq_one X t.G (eSec t.G) hsec hsemi.smooth hgi hga) (fun g => ⟨hw g, he g⟩) hfib
    t.PP.isLB ⟨t.PP.rig, t.PP.rigGen⟩ hL
  have hQ' := (quotient_flat_baseChange Γ X X' _ _ ρ π φ t.G.hom G'.hom hQ hpb inferInstance).2 τ
    fun g => ⟨hinv g, hw g⟩
  obtain ⟨L', hL', hiso⟩ := LinDescent.exists_descent_of_tame Γ _ _ τ φ t.PP.L hQ' (fun k _ _ y => by
    convert htame k (y ≫ t.G.hom) using 2
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g =>
      fixes_iff_fixes_image t.G.hom _ _ y (hw g) (hfib k _ g))) t.PP.isLB u hu₁ hu₂ hu₃
  obtain ⟨t', ν, e, hν⟩ := _root_.GlobalTheory.QuotTriple.exists_sab_of_quotient E H Γ X X' ρ π t G' a' φ L' hQ hga hsemi' hgp ha hL' hiso
  have hinv' (g : Γ) : (τ g).asIso.hom ≫ ν.φ = ν.φ := by
    rw [← cancel_mono e.hom.left, Category.assoc, hν, hinv]
  refine ⟨t', ν, hinv', fun ⟨h₁, h₂, _⟩ hP => ⟨?_, ?_, ?_⟩⟩
  · exact (SemiAbelianDescent.main X X' π t.G t'.G ν.φ inferInstance hsurj ν.cart t'.semi.smooth hsemi).2 h₁
  · exact splitFibres_descend_of_tame_quotient Γ X X' ρ π t.G t'.G ν.φ hQ htame ν.cart h₂
  · obtain ⟨w, hw', -⟩ := ν.lin
    have := t'.semi.smooth
    exact exists_secOn_nonvanishing_of_tame_quotient Γ X X' ρ π t.G t'.G ν.φ τ t.PP.L t'.PP.L hQ ν.cart.1
      inferInstance (fun g => ⟨hinv' g, hw g⟩) htame hfib t.PP.isLB t'.PP.isLB ⟨w, hw'⟩ hP

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymmetricBiadditiveBundleEighthPower
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.EighthPower

open GlobalTheory.CechPic Matrix

theorem map_prod_add {G M : Type*} [CommGroup G] [AddCommGroup M] (f : G → M) (hf : ∀ x y, f (x * y) = f x + f y)
    {n : ℕ} (x : Fin n → G) : f (∏ i, x i) = ∑ i, f (x i) := by
  simpa only [zpow_one, one_smul] using GlobalTheory.BilinCalc.map_prod_zpow f hf x fun _ => 1

theorem map_zpow_add {G M : Type*} [CommGroup G] [AddCommGroup M] (f : G → M) (hf : ∀ x y, f (x * y) = f x + f y)
    (x : G) (c : ℤ) : f (x ^ c) = c • f x := by
  simpa only [Fin.prod_univ_one, Fin.sum_univ_one] using
    GlobalTheory.BilinCalc.map_prod_zpow f hf (n := 1) (fun _ => x) fun _ => c

section Points

variable {S : Scheme.{0}} {G A T T' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]

theorem comp_prod_zpow (h : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ A)) (c : Fin n → ℤ) :
    h ≫ (∏ i, x i ^ c i) = ∏ i, (h ≫ x i) ^ c i := by
  let F : (T ⟶ A) →* (T' ⟶ A) := MonoidHom.mk' (fun z => h ≫ z) fun a b => MonObj.comp_mul _ _ _
  have e : F (∏ i, x i ^ c i) = ∏ i, F (x i) ^ c i := by simp only [map_prod, map_zpow]
  exact e

theorem prod_comp_hom (f : G ⟶ A) [IsMonHom f] {n : ℕ} (x : Fin n → (T ⟶ G)) :
    (∏ i, x i) ≫ f = ∏ i, x i ≫ f := by
  let F : (T ⟶ G) →* (T ⟶ A) := MonoidHom.mk' (fun z => z ≫ f) fun a b => MonObj.mul_comp _ _ _
  exact map_prod F x _

omit [IsCommMonObj A] in
theorem comp_id_zpow (x : T ⟶ A) (c : ℤ) : x ≫ (𝟙 A ^ c) = x ^ c := by
  let F : (A ⟶ A) →* (T ⟶ A) := MonoidHom.mk' (fun z => x ≫ z) fun a b => MonObj.comp_mul _ _ _
  have e : F (𝟙 A ^ c) = F (𝟙 A) ^ c := map_zpow F _ _
  exact e.trans (congrArg (· ^ c) (Category.comp_id x))

end Points

theorem prod_zpow_eq {H : Type*} [CommGroup H] (x : H) {n : ℕ} (c : Fin n → ℤ) : ∏ i, x ^ c i = x ^ ∑ i, c i := by
  have h := map_prod (zpowersHom H x) (fun i => Multiplicative.ofAdd (c i)) Finset.univ
  simp only [zpowersHom_apply, toAdd_prod, toAdd_ofAdd] at h
  exact h.symm

theorem main : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (ρ : Matrix (Fin 8) (Fin 8) ℤ → (G ⟶ G)), IsE8 W → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → (∃ t : LB.Gen (Theta G L), t.IsGen) → (∀ m u, ρ m ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) → (∀ m m', m.transpose * (W + W.transpose) = (W + W.transpose) * m' → LBIso (cubeLB G ![fst G G ≫ ρ m, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ ρ m'] L)) → (∀ m, (W + W.transpose) * m = W → LBIso L (cubeLB G ![𝟙 G, ρ m] L)) → ∃ P : LB (G2 A).left, P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧ (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) ∧ LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  intro W S G A _ _ _ _ pr L ρ hE hpr huniv hL hΘ hρ hadj hprim
  obtain ⟨B, hB⟩ : ∃ B, B = W + W.transpose := ⟨_, rfl⟩
  have hdet : IsUnit B.det := by rw [hB, hE.2]; exact isUnit_one
  have hBs : B.transpose = B := by rw [hB, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  rw [← hB] at hadj hprim
  have hBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hdet
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : Fin 8 → ℤ, u₀ = Pi.single 0 1 := ⟨_, rfl⟩
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : Fin 8 → ℤ, B *ᵥ u₁ = u₀ := ⟨B⁻¹ *ᵥ u₀, by rw [Matrix.mulVec_mulVec, hBi, Matrix.one_mulVec]⟩
  have h00 : u₀ ⬝ᵥ u₀ = 1 := by rw [hu₀]; simp
  have hsymB : ∀ v v' : Fin 8 → ℤ, v ⬝ᵥ B *ᵥ v' = v' ⬝ᵥ B *ᵥ v := fun v v' => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hBs, dotProduct_comm]
  have ext : ∀ {T : Over S} (x x' : T ⟶ G), (∀ u, x ≫ pr u = x' ≫ pr u) → x = x' := fun {T} x x' h =>
    (huniv T fun u => x' ≫ pr u).unique h fun _ => rfl
  choose ψ hψ using fun v : Fin 8 → ℤ => (huniv A fun u => 𝟙 A ^ v u).exists
  have hψ' : ∀ {T : Over S} (x : T ⟶ A) v u, (x ≫ ψ v) ≫ pr u = x ^ v u := fun x v u => by
    rw [Category.assoc, hψ, comp_id_zpow]
  have ψmul : ∀ {T : Over S} (x y : T ⟶ A) v, (x * y) ≫ ψ v = (x ≫ ψ v) * (y ≫ ψ v) := fun x y v =>
    ext _ _ fun u => by rw [hψ', MonObj.mul_comp, hψ', hψ', _root_.mul_zpow]
  have ψone : ∀ {T : Over S} v, (1 : T ⟶ A) ≫ ψ v = 1 := fun v =>
    ext _ _ fun u => by rw [hψ', MonObj.one_comp, _root_.one_zpow]
  have ψsmul : ∀ {T : Over S} (x : T ⟶ A) (c : ℤ) v, x ≫ ψ (c • v) = (x ^ c) ≫ ψ v := fun x c v =>
    ext _ _ fun u => by rw [hψ', hψ', ← _root_.zpow_mul, Pi.smul_apply, smul_eq_mul]
  have ψρ : ∀ {T : Over S} (x : T ⟶ A) v m, (x ≫ ψ v) ≫ ρ m = x ≫ ψ (m *ᵥ v) := fun x v m =>
    ext _ _ fun u => by
      rw [hψ', Category.assoc, hρ, List.prod_ofFn, comp_prod_zpow]
      simp only [hψ', ← _root_.zpow_mul, prod_zpow_eq]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have ρdec : ∀ m, ρ m = ∏ v, pr v ≫ ψ (m *ᵥ Pi.single v 1) := fun m =>
    ext _ _ fun u => by
      rw [hρ, List.prod_ofFn, prod_comp_hom]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [hψ']
      simp
  have iddec : 𝟙 G = ∏ v, pr v ≫ ψ (Pi.single v 1) :=
    ext _ _ fun u => by
      rw [Category.id_comp, prod_comp_hom, Finset.prod_eq_single u (fun b _ hb => by
        rw [hψ', Pi.single_eq_of_ne' hb, zpow_zero]) (by simp), hψ', Pi.single_eq_same, zpow_one]
  have lamL : ∀ {T : Over S} (x y z : T ⟶ G),
      lam (cls L hL) (x * y) z = lam (cls L hL) x z + lam (cls L hL) y z := by
    intro T x y z
    have h₀ := (cls_eq_zero_iff (N := Theta G L) (LB.isLB_linComb hL _ _)).2 hΘ
    have h₁ := (cls_cube_three hL (fst _ _) (snd _ _ ≫ fst _ _) (snd G (G ⊗ G) ≫ snd _ _)
      (LB.isLB_linComb hL _ _)).symm.trans h₀
    have h₂ := congrArg (pull (lift x (lift y z)).left) h₁
    simp only [map_sub, map_zero, pull_lam, MonObj.comp_mul, lift_fst, lift_snd_assoc, lift_snd] at h₂
    rw [sub_sub, sub_eq_zero] at h₂
    exact h₂
  obtain ⟨l, hl⟩ : ∃ l, l = cls L hL := ⟨_, rfl⟩
  rw [← hl] at lamL
  have lamR : ∀ {T : Over S} (x y z : T ⟶ G), lam l z (x * y) = lam l z x + lam l z y := fun x y z => by
    rw [lam_comm, lamL, lam_comm l x, lam_comm l y]
  have adj : ∀ {T : Over S} (x y : T ⟶ G) m m', m.transpose * B = B * m' →
      lam l (x ≫ ρ m) y = lam l x (y ≫ ρ m') := by
    intro T x y m m' hm
    have h := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (hadj m m' hm)
    have h' := congrArg (pull (lift x y).left)
      ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, ← hl] using h'
  obtain ⟨p, hp⟩ : ∃ p : ∀ {T : Over S}, (T ⟶ A) → (T ⟶ A) → Pic T.left,
      ∀ {T : Over S} (x y : T ⟶ A), p x y = lam l (x ≫ ψ u₀) (y ≫ ψ u₁) := ⟨_, fun _ _ => rfl⟩
  have pL : ∀ {T : Over S} (x x' y : T ⟶ A), p (x * x') y = p x y + p x' y := fun x x' y => by
    rw [hp, hp, hp, ψmul, lamL]
  have pR : ∀ {T : Over S} (x x' y : T ⟶ A), p y (x * x') = p y x + p y x' := fun x x' y => by
    rw [hp, hp, hp, ψmul, lamR]
  have key : ∀ {T : Over S} (x y : T ⟶ A) v v', lam l (x ≫ ψ v) (y ≫ ψ v') = (v ⬝ᵥ B *ᵥ v') • p x y := by
    intro T x y v v'
    have h := adj (x ≫ ψ u₀) (y ≫ ψ v') (vecMulVec v u₀) (vecMulVec u₁ (B *ᵥ v)) (by
      rw [Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec, hu₁, ← Matrix.mulVec_transpose, hBs])
    have e₁ : vecMulVec v u₀ *ᵥ u₀ = v := by
      rw [Matrix.vecMulVec_mulVec, h00]; simp
    have e₂ : vecMulVec u₁ (B *ᵥ v) *ᵥ v' = (v ⬝ᵥ B *ᵥ v') • u₁ := by
      rw [Matrix.vecMulVec_mulVec, dotProduct_comm, hsymB v' v]; simp
    rw [ψρ, ψρ, e₁, e₂, ψsmul, ← hp] at h
    rw [h]
    exact map_zpow_add (fun z => p x z) (fun a b => pR a b x) y _
  have pS : ∀ {T : Over S} (x y : T ⟶ A), p y x = p x y := fun x y => by
    rw [hp, lam_comm, key, hsymB, hu₁, h00, one_smul]
  have hP : (cubeLB G ![fst A A ≫ ψ u₀, snd A A ≫ ψ u₁] L).IsLB := LB.isLB_linComb hL _ _
  have hc : cls _ hP = p (fst A A) (snd A A) := by rw [cls_cube_two hL, hp, hl]
  have hpull : ∀ {T : Over S} (x y : T ⟶ A), pull (lift x y).left (cls _ hP) = p x y := fun x y => by
    rw [hc, hp, hp, pull_lam, lift_fst_assoc, lift_snd_assoc]
  refine ⟨cubeLB G ![fst A A ≫ ψ u₀, snd A A ≫ ψ u₁] L, hP, ?_, ?_, ?_, fun T x x' y => ⟨?_, ?_⟩, ?_⟩
  · refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
    rw [cls_pull hP, hpull, hp, ψone, lam_one_left]
  · refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
    rw [cls_pull hP, hpull, hp, ψone, lam_one_right]
  · refine (cls_eq_iff hP (pull_isLB hP _)).1 ?_
    rw [cls_pull hP, hpull, hc, pS]
  · refine (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).1 ?_
    rw [cls_linComb hP, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul, hpull, pL]
    abel
  · refine (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).1 ?_
    rw [cls_linComb hP, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul, hpull, pR]
    abel
  · refine (cls_eq_iff hL (LB.isLB_linComb hP _ _)).1 ?_
    have hw : B * (B⁻¹ * W) = W := by rw [← Matrix.mul_assoc, hBi, Matrix.one_mul]
    have h := ((cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 (hprim _ hw)).trans (cls_cube_two hL _ _ _)
    rw [cls_linComb hP, h, ← hl, Fintype.sum_prod_type, iddec, ρdec,
      map_prod_add (fun z => lam l z _) (fun a b => lamL a b _)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_prod_add (fun z => lam l _ z) (fun a b => lamR a b _)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [key, hpull, Matrix.mulVec_mulVec, hw]
    congr 1
    simp

end GlobalTheory.EighthPower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaObjPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left}

theorem pushHom_injective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Injective (pushHom h T) :=
  fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) (by rw [Over.w, Over.w]))

theorem pushHom_surjective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Surjective (pushHom h T) :=
  fun y => ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem map_linComb {T : Over S} {T' : Over S'} (ρ : (T' ⟶ A') →* (T ⟶ A)) {n : ℕ} (y : Fin n → (T' ⟶ A'))
    (a : Fin n → ℕ) : ρ (Out.linComb y a) = Out.linComb (fun i => ρ (y i)) a := by
  unfold Out.linComb
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact map_pow ρ _ _

def toBase (f : S' ⟶ S) : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S := Over.homMk f (by simp)

theorem exists_sec (h : IsGrpPullback A' A f φ) (x : Out.baseOver S ⟶ A) :
    ∃ x' : Out.baseOver S' ⟶ A', pushHom h _ x' = toBase f ≫ x :=
  pushHom_surjective h _ _

end GlobalTheory.ThetaObjPull

namespace GlobalTheory

open ThetaObjPull PolBaseChange

theorem tObj_pull : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' : Scheme.{0})
    (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s), f ≫ s = s' →
    ∃ t' : TObj g k J b s', TMap t' t f := by
  intro o _ g k J b S S' s s' f t hs
  subst hs
  have h := isGrpPullback_pullback t.A f
  have hL' := pull_isLB t.isLB (pullback.fst t.A.hom f)
  have hiso := lbIso_refl hL'
  obtain ⟨hab, hamp, hk⟩ := pol_pull _ _ _ _ _ _ _ _ t.isLB hL' t.ab h hiso
  choose pt hpt using fun i => exists_sec h (t.pt i)
  have hpt' : ∀ i, (pt i).left ≫ pullback.fst t.A.hom f = f ≫ (t.pt i).left := fun i =>
    congrArg (fun z => z.left) (hpt i)
  have := t.hom
  have := t.ab.comm
  refine ⟨{ A := (Over.pullback f).obj t.A
            ab := hab
            dim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 t.dim
            L := t.L.pull (pullback.fst t.A.hom f)
            isLB := hL'
            rigid := rigidified_pull h t.rigid
            sym := sym_pull h t.sym
            ample := hamp t.ample
            ktriv := hk t.ktriv
            pt := pt
            torsion := fun i => pushHom_injective h _ ?_
            bij := fun K _ _ x y hy => ?_
            pairing := fun i j => ?_
            act := fun j => (Over.pullback f).map (t.act j)
            hom := fun j => inferInstance }, pullback.fst t.A.hom f, h, hiso, hpt', fun j => pullback.lift_fst _ _ _⟩
  · rw [map_pow, map_one, hpt]
    exact (map_pow (preHom (toBase f)) _ _).symm.trans (by rw [t.torsion, map_one])
  · have key : ∀ c : Ix g k, pushHom h (Over.mk x) (Out.linComb (fun i =>
        (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S') ≫ pt i) (fun i => (c i).val)) =
        Out.linComb (fun i => (Over.homMk (x ≫ f) (by simp) : Over.mk (x ≫ f) ⟶ Out.baseOver S) ≫ t.pt i)
          (fun i => (c i).val) := fun c => by
      rw [map_linComb]
      congr 1
      funext i
      apply Over.OverMorphism.ext
      show (x ≫ (pt i).left) ≫ _ = (x ≫ f) ≫ (t.pt i).left
      rw [Category.assoc, hpt', Category.assoc]
    have hy' : pushHom h (Over.mk x) y ^ k = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨c, hc, hu⟩ := t.bij K (x ≫ f) (pushHom h (Over.mk x) y) hy'
    exact ⟨c, pushHom_injective h _ ((key c).trans hc), fun c' hc' => hu c' ((key c').symm.trans (congrArg _ hc'))⟩
  · refine (weilIs_grpPullback_of_comm _ _ _ _ f _ _ _ t.isLB hL' h hiso (Out.baseOver S') k (pt i) (pt j)
      (toBase f ≫ t.pt i) (toBase f ≫ t.pt j) _ (hpt' i).symm (hpt' j).symm).2 ?_
    have w := CommPairing.weilIs_pull globalFns_holds t.ab t.isLB (toBase f) (t.pairing i j)
    rw [map_zpow] at w
    have e : Units.map (toBase f).left.appTop.hom.toMonoidHom (unitS s b.ζ) = unitS (f ≫ s) b.ζ := by
      apply Units.ext
      show f.appTop.hom (s.appTop.hom _) = (f ≫ s).appTop.hom _
      rw [Scheme.Hom.comp_appTop]
      rfl
    exact e ▸ w

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckePointsOfParts
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem fibPt_injective {X : Scheme.{0}} (G : Over X) {k : Type} [Field k] {y : Sp k ⟶ X} :
    Function.Injective (fibPt G (y := y)) := fun a b h => Over.OverMorphism.ext (by
  have := congrArg (· ≫ pullback.fst G.hom y) h
  simpa only [fibPt, pullback.lift_fst] using this)

end GlobalTheory.HeckePoint

namespace GlobalTheory

open HeckePoint

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreOrbit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.levelMap_fibre_orbit : Out.Laws → (∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing
    B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s'
    : S' ⟶ Sp B') (f
    : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap
    o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l
    : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b'
    : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s''
    : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o''
    : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f'
    : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫
    f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫
    f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
    : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p
    + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B
    : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o₂
    : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (o : Obj D l b s) (m
    : SABMap o₂.t o.t (𝟙 S)), (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta
    a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B'
    : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s
    : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S'
    ∨ IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta
    a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ) → (∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (B
    : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA
    l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (k : Type) [Field
    k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e
    : ℕ → Q → Q → kˣ → Prop), (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → ∀ I I' : TateIso D k Q act e, ∃ g : Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f
    n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n
    : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n
    : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f
    n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo
    : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK
    : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l)
    : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M /
    l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A /
    l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA
    a).left) → ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r) → ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo
    : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK
    : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l)
    : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M /
    l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A /
    l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc
    : c.F = c₂.F) (rF
    : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion
    hc.le).toRingHom → ∀ (k : Type) [Field k] [IsAlgClosed k] (y y'
    : Sp k ⟶ Xo₂.XF c₂), y ≫ rF = y' ≫ rF → (∃ (g : Sim D) (ρ
    : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ ∧ Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r ∧ y' ≫ pullback.fst _ _ = y ≫ pullback.fst _ _ ≫ ρ.hom) ∧ ∀ (g
    : Sim D) (ρ
    : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ → Xo₂.LevAut g ρ → y ≫ pullback.fst _ _ ≫ ρ.hom = y ≫ pullback.fst _ _ → g.TrivAt l₂ :=
  GlobalTheory.LevelFibre.levelMap_fibre_simply_transitive_of_laws
end

