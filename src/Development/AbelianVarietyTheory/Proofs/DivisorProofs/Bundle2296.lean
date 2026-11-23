module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfCompEq
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem locInt_le_chart {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j) :
    α ⁻¹ᵁ W ≤ LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hW hy

theorem locInt_le_gen {S G Y T : Scheme.{0}} (g : G ⟶ S) (α : Y ⟶ G) (t : Y ⟶ T) (e : T ⟶ S)
    (hpb : α ≫ g = t ≫ e) (W : G.Opens) (U : S.Opens) (hWU : W ≤ g ⁻¹ᵁ U) :
    α ⁻¹ᵁ W ≤ t ⁻¹ᵁ (e ⁻¹ᵁ U) := by
  intro y hy
  have h1 : g (α y) ∈ U := hWU hy
  have h2 : (α ≫ g) y = (t ≫ e) y := by rw [hpb]
  show e (t y) ∈ U
  rw [← Scheme.Hom.comp_apply, ← h2]
  exact h1

def LocInt {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S) (L : LB G.left) {Y : Scheme.{0}}
    (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : α ≫ G.hom = t ≫ M.gp) {k : ℕ} (s : SecK L α k) : Prop :=
  ∀ (j : L.ι) (W : G.left.Opens) (U : M.S.Opens) (hW : W ≤ L.U j) (hWU : W ≤ G.hom ⁻¹ᵁ U),
    IsAffineOpen W → IsAffineOpen U →
    ∃ (n : ℕ) (c : Fin n → Γ(G.left, W)) (b : Fin n → Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)),
      (∀ m, (M.gp.app U).hom.IsIntegralElem (b m)) ∧
      (Y.presheaf.map (homOfLE (locInt_le_chart L α j W hW)).op).hom (s.f (fun _ => j)) =
        ∑ m, (α.app W).hom (c m) * (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen G.hom α t M.gp hpb W U hWU)).hom (b m)

theorem le_preimage_of_comp_eq {X X' S : Scheme.{0}} (g : X ⟶ S) (g' : X ⟶ X') (h : X' ⟶ S) (e : g' ≫ h = g)
    (U : S.Opens) : g ⁻¹ᵁ U ≤ g' ⁻¹ᵁ (h ⁻¹ᵁ U) := by
  intro x hx
  show h (g' x) ∈ U
  rw [← Scheme.Hom.comp_apply, e]
  exact hx

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeastVectorUniqueInClassMod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.LeastVec

def cross {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (x y : Fin s → X) : ℤ :=
  ∑ u, ∑ v, W u v * (β (x u) (y v) + β (y u) (x v))

theorem qW_add_zsmul {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (x y : Fin s → X) (n : ℤ) :
    qW W β (x + n • y) = qW W β x + n * cross W β x y + n ^ 2 * qW W β y := by
  unfold qW cross
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, map_add (f := _), LinearMap.add_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem least_lt_add_smul : ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∀ (X : Type) [AddCommGroup X] (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → ∀ (H : AddSubgroup (Fin s → X)), (∀ mu ∈ H, mu ≠ 0 → 0 < qW W β mu) → ∀ mu₀ ∈ H, mu₀ ≠ 0 → (∀ mu ∈ H, mu ≠ 0 → qW W β mu₀ ≤ qW W β mu) → ∀ N₁ : ℕ, 3 ≤ N₁ → ∀ nu ∈ H, nu ≠ 0 → qW W β mu₀ < qW W β (mu₀ + N₁ • nu) := by
  intro s W hW X _ β hs hβ H hpos mu₀ hmu₀ _ hmin N₁ hN nu hnu hnu0
  have hq := qW_add_zsmul W β mu₀ nu
  have h1 : 0 ≤ qW W β (mu₀ + nu) := qW_nonneg hW hs hβ _
  rw [← one_zsmul nu, hq 1] at h1
  simp only [one_mul, one_pow] at h1
  have hN' : qW W β (mu₀ + N₁ • nu) = qW W β mu₀ + (N₁ : ℤ) * cross W β mu₀ nu + (N₁ : ℤ) ^ 2 * qW W β nu := by
    rw [← hq, natCast_zsmul]
  rw [hN']
  have hle := hmin nu hnu hnu0
  have hp := hpos nu hnu hnu0
  have hN3 : (3 : ℤ) ≤ N₁ := by exact_mod_cast hN
  set B := cross W β mu₀ nu
  set q0 := qW W β mu₀
  set qn := qW W β nu
  have hNn : (0 : ℤ) ≤ N₁ := by omega
  have e1 : (N₁ : ℤ) * (-q0 - qn) ≤ (N₁ : ℤ) * B := mul_le_mul_of_nonneg_left (by linarith) hNn
  have e2 : (N₁ : ℤ) * q0 ≤ (N₁ : ℤ) * qn := mul_le_mul_of_nonneg_left hle hNn
  have e3 : 0 < (N₁ : ℤ) * ((N₁ : ℤ) - 2) * qn := by
    apply mul_pos (mul_pos (by omega) (by omega)) hp
  nlinarith

end GlobalTheory.Poinc.LeastVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftImmersionOfReduced
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem lift_immersion_of_reduced : ∀ (X Y P : Scheme.{0}) (f : X ⟶ P) (j : Y ⟶ P), IsReduced X → IsImmersion j → Set.range f ⊆ Set.range j → ∃ g : X ⟶ Y, g ≫ j = f := by
  intro X Y P f j _ _ hfj
  have hr : Set.range f ⊆ Set.range (j.coborderRange).ι := by
    intro x hx
    obtain ⟨y, rfl⟩ := hfj hx
    exact ⟨j.liftCoborder y, by rw [← Scheme.Hom.comp_apply, Scheme.Hom.liftCoborder_ι]⟩
  let f' := IsOpenImmersion.lift (j.coborderRange).ι f hr
  have hf' : f' ≫ (j.coborderRange).ι = f := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ := GlobalTheory.exists_lift_closedImmersion_of_dense j.liftCoborder f' Set.univ dense_univ
    (fun x _ ↦ by
      obtain ⟨y, hy⟩ := hfj ⟨x, rfl⟩
      refine ⟨y, (j.coborderRange).ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.liftCoborder_ι, hy, ← Scheme.Hom.comp_apply, hf'])
  exact ⟨g, by rw [← Scheme.Hom.liftCoborder_ι j, ← Category.assoc, hg, hf']⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftToProjectiveBaseInjectiveOverClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Emb.chart_injective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∀ z w : E.H.toScheme, M.π (G'.hom (E.H.ι z)) = closedPoint R → pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over w = pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over z → w = z := by
  intro R _ _ _ _ M G' _ _ _ E z w hz hwz

  set p := PSpace.str R E.N
  set Φ : E.H.toScheme ⟶ pullback p M.π := pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over with hΦ
  set s := G'.hom (E.H.ι z) with hs

  let Ω := M.S.residueField s
  let x : Sp Ω ⟶ M.S := M.S.fromSpecResidueField s
  let φ : R →+* Ω := (Spec.preimage (x ≫ M.π)).hom
  have hφ : spMap φ = x ≫ M.π := by unfold spMap; simp [φ]
  have hker : ∀ r ∈ maximalIdeal R, φ r = 0 := by
    intro r hr
    obtain ⟨pt⟩ : Nonempty (Sp Ω) := inferInstance
    have h1 : (x ≫ M.π) pt = closedPoint R := by
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]; exact hz
    rw [← hφ] at h1
    have h2 : (spMap φ) pt = PrimeSpectrum.comap φ pt := rfl
    have h3 : pt.asIdeal = ⊥ := by haveI := pt.isPrime; exact Ideal.eq_bot_of_prime _
    have h4 : r ∈ ((spMap φ) pt).asIdeal := by rw [h1]; exact hr
    rw [h2] at h4
    change φ r ∈ pt.asIdeal at h4
    rw [h3] at h4
    exact h4
  let κ : ResidueField R →+* Ω := Ideal.Quotient.lift (maximalIdeal R) φ hker
  have hκ : κ.comp (residue R) = φ := by ext r; rfl
  have hx : x ≫ M.π = spMap (κ.comp (residue R)) := by rw [hκ, hφ]
  obtain ⟨Ω', _, io, e, l, -, hl, hlf⟩ := E.fib Ω x κ hx

  have hx'π : (spMap io ≫ x) ≫ M.π = spMap (io.comp κ) ≫ spMap (residue R) := by
    rw [Category.assoc, hx]; unfold spMap; rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  have hψ : (l ≫ Φ) ≫ pullback.snd p M.π = pullback.snd G'.hom (spMap io ≫ x) ≫ (spMap io ≫ x) := by
    have : Φ ≫ pullback.snd p M.π = E.H.ι ≫ G'.hom := by rw [hΦ]; exact pullback.lift_snd _ _ _
    rw [Category.assoc, this, ← Category.assoc, hl]; exact pullback.condition
  let ψ : pullback G'.hom (spMap io ≫ x) ⟶ pullback (pullback.snd p M.π) (spMap io ≫ x) :=
    pullback.lift (l ≫ Φ) (pullback.snd _ _) hψ

  have hψinj : Function.Injective ψ := by
    haveI : IsImmersion E.j := E.imm
    let h : pullback (pullback.snd p M.π) (spMap io ≫ x) ⟶ PSpace R E.N := pullback.fst _ _ ≫ pullback.fst _ _
    have hΦf : Φ ≫ pullback.fst p M.π = E.f := by rw [hΦ]; exact pullback.lift_fst _ _ _
    have hψ1 : ψ ≫ pullback.fst _ _ = l ≫ Φ := pullback.lift_fst _ _ _
    have hψh : ψ ≫ h = l ≫ E.f := by
      show ψ ≫ pullback.fst _ _ ≫ pullback.fst _ _ = _
      rw [← Category.assoc, hψ1, Category.assoc, hΦf]
    have hθ : (e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ))) ≫ E.j = ψ ≫ h := by
      rw [hψh, hlf, Category.assoc]
    let θ : pullback G'.hom (spMap io ≫ x) ⟶ pullback E.j h := pullback.lift _ _ hθ
    haveI : Mono (spMap (residue R)) := by
      have : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
      infer_instance
    have hΦs : Φ ≫ pullback.snd p M.π = E.H.ι ≫ G'.hom := by rw [hΦ]; exact pullback.lift_snd _ _ _
    have hρ : pullback.fst E.j h ≫ E.Y.hom = (pullback.snd E.j h ≫ pullback.snd _ _) ≫ spMap (io.comp κ) := by
      rw [← cancel_mono (spMap (residue R))]
      calc pullback.fst E.j h ≫ E.Y.hom ≫ spMap (residue R) = pullback.fst E.j h ≫ E.j ≫ p := by rw [E.j_over]
        _ = pullback.snd E.j h ≫ h ≫ p := by rw [← Category.assoc, pullback.condition, Category.assoc]
        _ = pullback.snd E.j h ≫ pullback.fst _ _ ≫ pullback.snd p M.π ≫ M.π := by
          simp only [h, Category.assoc]; rw [pullback.condition]
        _ = pullback.snd E.j h ≫ pullback.snd _ _ ≫ (spMap io ≫ x) ≫ M.π := by
          rw [← Category.assoc (pullback.fst _ _), pullback.condition, Category.assoc]
        _ = ((pullback.snd E.j h ≫ pullback.snd _ _) ≫ spMap (io.comp κ)) ≫ spMap (residue R) := by
          rw [hx'π]; simp only [Category.assoc]
    let ρ : pullback E.j h ⟶ pullback E.Y.hom (spMap (io.comp κ)) := pullback.lift _ _ hρ
    have hθ1 : θ ≫ pullback.fst E.j h = e.hom.left ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
    have hθ2 : θ ≫ pullback.snd E.j h = ψ := pullback.lift_snd _ _ _
    have hρ1 : ρ ≫ pullback.fst _ _ = pullback.fst E.j h := pullback.lift_fst _ _ _
    have hρ2 : ρ ≫ pullback.snd _ _ = pullback.snd E.j h ≫ pullback.snd _ _ := pullback.lift_snd _ _ _
    have hψ2 : ψ ≫ pullback.snd _ _ = pullback.snd G'.hom (spMap io ≫ x) := pullback.lift_snd _ _ _
    have hθρ : θ ≫ ρ = e.hom.left := by
      apply pullback.hom_ext
      · rw [Category.assoc, hρ1, hθ1]
      · rw [Category.assoc, hρ2, ← Category.assoc, hθ2, hψ2]
        exact (Over.w e.hom).symm
    intro a b hab
    have h1 : θ a = θ b := by
      apply (pullback.snd E.j h).isEmbedding.injective
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd]; exact hab
    have h2 : e.hom.left a = e.hom.left b := by
      rw [← hθρ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h1]
    have h3 := congrArg e.inv.left h2
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, e.hom_inv_id, Over.id_left] at h3

  obtain ⟨τ⟩ : Nonempty (Sp Ω') := inferInstance
  have hτ : (spMap io ≫ x) τ = s := by
    rw [Scheme.Hom.comp_apply]; exact Scheme.fromSpecResidueField_apply _ _
  have hΦs : Φ ≫ pullback.snd p M.π = E.H.ι ≫ G'.hom := by rw [hΦ]; exact pullback.lift_snd _ _ _
  have hq : pullback.snd p M.π (Φ z) = (spMap io ≫ x) τ := by
    rw [hτ, ← Scheme.Hom.comp_apply, hΦs, Scheme.Hom.comp_apply]
  obtain ⟨c, hc1, hc2⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd p M.π) (g := spMap io ≫ x) _ _ hq

  have hm : (pullback.fst Φ (pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) ≫ E.H.ι) ≫ G'.hom =
      (pullback.snd Φ (pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) ≫ pullback.snd _ _) ≫ (spMap io ≫ x) := by
    rw [Category.assoc, ← hΦs, ← Category.assoc, pullback.condition, Category.assoc, pullback.condition,
      Category.assoc]
  let m : pullback Φ (pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) ⟶ pullback G'.hom (spMap io ≫ x) :=
    pullback.lift _ _ hm
  have hm1 : m ≫ l = pullback.fst _ _ := by
    rw [← cancel_mono E.H.ι, Category.assoc, hl]; exact pullback.lift_fst _ _ _
  have hm2 : m ≫ ψ = pullback.snd _ _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hm1, pullback.condition]
    · rw [Category.assoc, pullback.lift_snd]; exact pullback.lift_snd _ _ _
  have lift_pt : ∀ u : E.H.toScheme, Φ u = Φ z → ∃ a, l a = u ∧ ψ a = c := by
    intro u hu
    obtain ⟨pu, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Φ) (g := pullback.fst (pullback.snd p M.π) (spMap io ≫ x)) u c (hu.trans hc1.symm)
    exact ⟨m pu, by rw [← Scheme.Hom.comp_apply, hm1, h1], by rw [← Scheme.Hom.comp_apply, hm2, h2]⟩
  obtain ⟨a, ha1, ha2⟩ := lift_pt w hwz
  obtain ⟨b, hb1, hb2⟩ := lift_pt z rfl
  rw [← ha1, ← hb1, hψinj (ha2.trans hb2.symm)]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsNaturalOfObstructionOneZero
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem exists_natural_lift_of_ob1_eq_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → Module.Projective R₀ (GlobForm s₀) → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsLift L' n l → (∀ w, L.IsOb1 L' n l α w 0) → ∃ l' : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T, L.IsLift L' n l' ∧ L.IsNat L' n l' := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ hpar hproj C' _ F' L L' n l hl h0
  obtain ⟨κ, u, hκ, hu, huI, hd⟩ := _root_.GlobalTheory.Obs.exists_cochain_of_isOb1_zero R R₀ I hI π hπ hk R₁ α X₀ s₀ hproj C' F' L L' n l h0
  exact _root_.GlobalTheory.LiftSys.exists_natLift_of_defect R R₀ I hI π hπ hk X₀ s₀ hpar C' F' L L' n l hl κ u hκ hu huI hd

end GlobalTheory.Obs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MumFam

def GAdj {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    (L₁ : LB G₁.left) (L₂ : LB G₂.left) (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁) : Prop :=
  LBIso (cubeLB G₂ ![fst G₁ G₂ ≫ u, snd G₁ G₂] L₂) (cubeLB G₁ ![fst G₁ G₂, snd G₁ G₂ ≫ u'] L₁)

def adjVal {S : Scheme.{0}} {T G₁ G₂ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    {L₁ : LB G₁.left} {L₂ : LB G₂.left} {x₁ : Fin 2 → (T ⟶ G₁)} {x₂ : Fin 2 → (T ⟶ G₂)}
    (w : LB.Iso (cubeLB G₂ x₂ L₂) (cubeLB G₁ x₁ L₁)) {Z : Scheme.{0}} (p : Z ⟶ T.left) (z : Z)
    (J₁ : (Z ⟶ G₁.left) → L₁.ι) (J₂ : (Z ⟶ G₂.left) → L₂.ι) : (Z.presheaf.stalk z)ˣ :=
  gm p z _ (w.s (fun I => J₁ (p ≫ (psum G₁ x₁ I.down).left), fun I => J₂ (p ≫ (psum G₂ x₂ I.down).left)))

variable {R : Type} [CommRing R] [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R']

def Adj (Q₁ Q₂ : Data R) (a : Q₁.B ⟶ Q₂.B) (a' : Q₂.B ⟶ Q₁.B) (h : Q₁.X →+ Q₂.X) (h' : Q₂.X →+ Q₁.X) : Prop :=
  IsMonHom a ∧ IsMonHom a' ∧ (∀ y, Q₂.c (h y) = Q₁.c y ≫ a) ∧ (∀ z, Q₁.c (h' z) = Q₂.c z ≫ a') ∧
  ∃ w : LB.Iso (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L)
      (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L), w.IsGen ∧
    ∀ y y' z J₁ J₂, Good Q₁.M.L z J₁ → Good Q₂.M.L z J₂ →
      val (Q₂.tau (h y) y') (𝟙 _) z J₂ =
        adjVal w (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left z J₁ J₂ * val (Q₁.tau y (h' y')) (𝟙 _) z J₁

abbrev pol {I : Ideal R} (D : DegData R I) : Data R := Wit.ofDeg D.toPre D.tau_bimult

def RefAt (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (β : D.P.A.left ⟶ Q.B.left) : Prop :=
  letI := D.P.isAb.comm
  ∃ (β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂)),
    IsGrpPullback D.P.A Q.B (spMap ρ) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) ∧
    ∀ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ → ∀ a b z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.tau a b) (𝟙 _) z J' =
        lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' * val (Q.tau (e a) (e b)) κ z J

def IsTens (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B))
    (xe : D'.X ≃+ (Fin r → Q.X)) : Prop :=
  (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk D'.P.A pr)) ∧ (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) ∧
  ∃ w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W)), w.IsGen ∧
    ∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' →
      val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j

def TorusHomOf {S : Scheme.{0}} {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂] (h : X₂ → X₁)
    (t : splitTorus S X₁ ⟶ splitTorus S X₂) : Prop :=
  ∀ χ : X₂, res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X₂ χ)) = charUnit S X₁ (h χ)

variable {I : Ideal R} {D₁ D₂ D₃ : DegData R I} {A₁ A₂ A₃ : PolAV (Sp (FractionRing R))} {G₁ G₂ G₃ : Over (Sp R)}
  [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] [GrpObj G₃] [IsCommMonObj G₃]

def LinHom (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : D₁.toPre.P.A ⟶ D₂.toPre.P.A)
    (h' : D₂.toPre.X →+ D₁.toPre.X) (g : G₁ ⟶ G₂) : Prop :=
  IsMonHom g ∧ (∀ e, (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map a) ∧
    ∀ e, ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.toPre.X,
      TorusHomOf h' t ∧ (U₁.gt e).i ≫ (Over.pullback (thick R I e)).map g = t ≫ (U₂.gt e).i

theorem TorusHomOf.comp {S : Scheme.{0}} {X₁ X₂ X₃ : Type} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
    {h : X₂ → X₁} {k : X₃ → X₂} {t : splitTorus S X₁ ⟶ splitTorus S X₂} {s : splitTorus S X₂ ⟶ splitTorus S X₃}
    (ht : TorusHomOf h t) (hs : TorusHomOf k s) : TorusHomOf (fun χ => h (k χ)) (t ≫ s) := fun χ => by
  rw [← ht (k χ), ← hs χ]
  refine unit_ext fun z _ => ?_
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_
  refine Eq.symm (((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_)
  refine ((gm_res _ z (V := ⊤) _ trivial _).trans (gm_pull _ _ z ⊤ trivial _)).trans ?_
  rfl

theorem TorusHomOf.id {S : Scheme.{0}} (X : Type) [AddCommGroup X] : TorusHomOf (fun χ : X => χ) (𝟙 (splitTorus S X)) :=
  fun χ => unit_ext fun z _ =>
    ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans rfl

theorem LinHom.id (U : UnifPre I D₁ A₁ G₁) : LinHom U U (𝟙 _) (AddMonoidHom.id _) (𝟙 G₁) :=
  ⟨inferInstance, fun e => by simp, fun e => ⟨𝟙 _, TorusHomOf.id _, by simp⟩⟩

theorem LinHom.comp {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂} {U₃ : UnifPre I D₃ A₃ G₃} {a h' g b k' f}
    (hg : LinHom U₁ U₂ a h' g) (hf : LinHom U₂ U₃ b k' f) : LinHom U₁ U₃ (a ≫ b) (h'.comp k') (g ≫ f) := by
  obtain ⟨g₁, g₂, g₃⟩ := hg
  obtain ⟨f₁, f₂, f₃⟩ := hf
  refine ⟨inferInstance, fun e => ?_, fun e => ?_⟩
  · rw [Functor.map_comp, Functor.map_comp, Category.assoc, f₂, ← Category.assoc, g₂, Category.assoc]
  · obtain ⟨t, ht, hi⟩ := g₃ e
    obtain ⟨s, hs, hj⟩ := f₃ e
    refine ⟨t ≫ s, ht.comp hs, ?_⟩
    rw [Functor.map_comp, ← Category.assoc, hi, Category.assoc, hj, Category.assoc]

theorem linHom_iff_linEnd {U : UnifPre I D₁ A₁ G₁} {a h' g} : LinHom U U a h' g ↔ LinEnd U a h' g := by
  refine ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, fun e => inferInstance, fun e => ?_, h₂, h₃⟩, fun ⟨h₁, _, _, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩
  apply pullback.hom_ext
  · simp only [thickMap, Over.pullback_map_left, Category.assoc, pullback.map]
    erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id, pullback.lift_fst]
  · simp only [thickMap, Over.pullback_map_left, Category.assoc, pullback.map]
    erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd_assoc]

end GlobalTheory.MumFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoGenericFibreDescendFiniteExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.Mum

theorem exists_comp_eq_fst {S S' U U' X X' : Scheme.{0}} {g : X ⟶ S} {g' : X' ⟶ S'} {s : S' ⟶ S} {β : X' ⟶ X}
    (pb : IsPullback β g' g s) {j : U ⟶ S} [Mono j] {j' : U' ⟶ S'} {u : U' ⟶ U} (sq : u ≫ j = j' ≫ s)
    (κ : pullback g' j' ⟶ pullback g j) (hκ : κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β) :
    ∃ c : pullback (pullback.snd g j) u ⟶ pullback g' j', c ≫ κ = pullback.fst _ _ := by
  have w : (pullback.fst (pullback.snd g j) u ≫ pullback.fst g j) ≫ g = (pullback.snd (pullback.snd g j) u ≫ j') ≫ s := by
    rw [Category.assoc, pullback.condition, pullback.condition_assoc, sq, Category.assoc]
  refine ⟨pullback.lift (pb.lift _ _ w) _ (pb.lift_snd _ _ w), ?_⟩
  rw [← cancel_mono (pullback.fst g j), Category.assoc, hκ, pullback.lift_fst_assoc, pb.lift_fst]

theorem lbIso_pull_pull_of_third {Q Y X Z Z' B : Scheme.{0}} {c : Q ⟶ Y} {κ : Y ⟶ X} {q : Q ⟶ X} (hc : c ≫ κ = q)
    {p : X ⟶ Z} {p' : Y ⟶ Z'} {β : Z' ⟶ Z} (hκ : κ ≫ p = p' ≫ β) {a : X ⟶ B} {M : LB B} {N : LB Z} {L' : LB Z'}
    (hM : M.IsLB) (hN : N.IsLB) (hL' : L'.IsLB) (h₁ : LBIso (L'.pull p') (M.pull (κ ≫ a))) (h₂ : LBIso L' (N.pull β)) :
    LBIso ((M.pull a).pull q) ((N.pull p).pull q) := by
  have hA := pull_isLB hM a
  have hP := pull_isLB hN p
  have e₁ : LBIso (L'.pull (c ≫ p')) (M.pull (q ≫ a)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp c rfl (by rw [← Category.assoc, hc]) h₁
  have e₂ : LBIso (L'.pull (c ≫ p')) (N.pull (q ≫ p)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso h₂ _ (by rw [Category.assoc, ← hκ, ← hc, Category.assoc])
  exact LBIso.trans (pull_isLB hA _) (pull_isLB hM _) (pull_isLB hP _)
    (GlobalTheory.GenSpread.lbIso_pull_pull hM q rfl).symm
    (LBIso.trans (pull_isLB hM _) (pull_isLB hL' _) (pull_isLB hP _) e₁.symm
      (LBIso.trans (pull_isLB hL' _) (pull_isLB hN _) (pull_isLB hP _) e₂
        (GlobalTheory.GenSpread.lbIso_pull_pull hN q rfl)))

theorem exists_fractionRing_map {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ) : ∃ g : FractionRing R →+* FractionRing R',
      g.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp ρ := by
  have hinj : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) :=
    fun a b h => hρ (IsFractionRing.injective R' (FractionRing R') h)
  exact ⟨IsFractionRing.lift (K := FractionRing R) hinj,
    RingHom.ext fun r => IsFractionRing.lift_algebraMap (K := FractionRing R) hinj r⟩

theorem lbIso_generic_descend : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G' → IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) (κ : pullback G'.hom (jK R') ⟶ pullback G.hom (jK R)), IsMonHom gen.hom → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β → ∀ (L' : LB G'.left), L'.IsLB → LBIso (L'.pull (pullback.fst G'.hom (jK R'))) (A.L.pull (κ ≫ gen.hom.left)) → ∀ P : GlobalTheory.UU.CP G, LBIso L' (P.L.L.pull β) → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  intro R _ _ _ _ R' _ _ _ ρ hρ G' _ _ G _ _ β _ _ pb A gen κ hgen hκ L' hL' h₁ P h₂
  obtain ⟨gam, hgam⟩ := exists_fractionRing_map ρ hρ.2.1
  have sq : spMap gam ≫ jK R = jK R' ≫ spMap ρ :=
    (spMap_comp _ gam).symm.trans ((congrArg spMap hgam).trans (spMap_comp ρ _))
  have hX : IsAbelianScheme ((Over.pullback (jK R)).obj G) :=
    GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback A.isAb (isGrpPullback_of_iso gen)
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  obtain ⟨c, hc⟩ := exists_comp_eq_fst pb.1 sq κ hκ
  exact GlobalTheory.PolIsoDescent.lbIso_descend GlobalTheory.globalFns_holds (spMap gam) _ hX (pull_isLB A.isLB _)
    (pull_isLB P.L.isLB _) (lbIso_pull_pull_of_third hc hκ A.isLB P.L.isLB hL' h₁ h₂)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OLinearLevelPullbackUniversalFactorisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oLinearLevel_pullback_universal_factorisation : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] (actH : OActN D.O AH) (Y : Over H) (u : D.La → (Y ⟶ AH)) (AE : Over Y.left) [GrpObj AE] (φE : AE.left ⟶ AH.left) (ηE : D.La → (𝟙_ (Over Y.left) ⟶ AE)), IsGrpPullback AE AH Y.hom φE → (∀ y, (ηE y).left ≫ φE = (u y).left) → (∀ (T : Over H) (u' : D.La → (T ⟶ AH)), (∀ x y, u' (x + y) = u' x * u' y) → (∀ (c : D.O) x, u' (c • x) = u' x ≫ actH.act c) → (∀ x, u' (N • x) = 1) → ∃! h : T ⟶ Y, ∀ x, h ≫ u x = u' x) → ∀ (T : Scheme.{0}) (g : T ⟶ H) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ AH.left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT AH g φ → (∀ a : D.O, (act.act a).left ≫ φ = φ ≫ (actH.act a).left) → EtaOK D N act eta → ∃! z : T ⟶ Y.left, z ≫ Y.hom = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  first | (exact @GlobalTheory.UPel.HT.pullUnivP) | (exact GlobalTheory.UPel.HT.pullUnivP) | (intros; apply GlobalTheory.UPel.HT.pullUnivP  <;> assumption)
end

