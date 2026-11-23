module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0040
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0044

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSmulEqSumMulOfIsDomain
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace KunnethDomain

open ReciprocityTheory.ChartRestriction.G.DVR

variable {X Y Y' T : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def cst {R : Type} [CommRing R] (q : T ⟶ Spec (CommRingCat.of R)) (z : T) : R →+* T.presheaf.stalk z :=
  (T.presheaf.germ ⊤ z trivial).hom.comp (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem gs_scal_eq {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (ρ : T ⟶ Y) (z : T) (c : R) :
    gs ρ z ⊤ (scal p c) = cst (ρ ≫ p) z c := by
  rw [gs_eq ρ z ⊤ trivial]; rfl

theorem sval_scale {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε))
    (r : T ⟶ Y) (z : T) {J} (hJ : Good L z J) :
    sval (SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

theorem sval_pull {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (r : T ⟶ Y') (z : T) {J} (hJ : Good L z J) : sval (pullSec L φ ε s h) r z J = sval s (r ≫ h) z J := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm := hJ.mem (fun k => h ≫ φ k) r
  exact (gs_res r z _ hm _).trans (gs_pull r h z (LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)))
    (wchart_comp_le φ h _ hm) _)

theorem sval_mul {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (r : T ⟶ Y) (z : T) {J} (hJ : Good L z J) :
    sval (mulSec L φ ε φ' ε' s s') r z J = sval s r z J * sval s' r z J :=
  have hm := hJ.mem (Sum.elim φ φ') r
  (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res r z _ hm _) (gs_res r z _ hm _))

def secSum {M : LB Y} {n : ℕ} (s : Fin n → LB.Sec M) : LB.Sec M where
  f := fun j => ∑ i, (s i).f j
  compat := fun j j' => by simp only [map_sum, (s _).compat, Finset.mul_sum]

theorem sval_sum {φ : K → (Y ⟶ X)} {ε : K → ℤ} {n : ℕ} (s : Fin n → LB.Sec (LB.LinComb L φ ε))
    (r : T ⟶ Y) (z : T) {J} (hJ : Good L z J) : sval (secSum s) r z J = ∑ i, sval (s i) r z J := by
  have hm := hJ.mem φ r
  refine (gs_eq r z _ hm _).trans (Eq.trans ?_ (Finset.sum_congr rfl fun i _ => (gs_eq r z _ hm _).symm))
  exact map_sum ((T.presheaf.germ (r ⁻¹ᵁ LB.wchart L φ fun k => J (r ≫ φ k)) z hm).hom.comp
    (r.app (LB.wchart L φ fun k => J (r ≫ φ k))).hom) (fun i => (s i).f fun k => J (r ≫ φ k)) Finset.univ

theorem sec_ext_of_app_injective (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (κ : Y' ⟶ Y) (hκ : ∀ U : Y.Opens, Function.Injective (κ.app U).hom)
    {u t : LB.Sec (LB.LinComb L φ ε)} (h : ∀ y J, Good L y J → sval u κ y J = sval t κ y J) : u = t :=
  SecOps.sec_ext fun j => by
    refine hκ (LB.wchart L φ j) (fn_ext fun y hy => ?_)
    choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ y)
    refine (gs_pull (𝟙 Y') κ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') κ y _ hy _).symm)
    rw [Category.id_comp]
    exact (sec_trans u κ y hy (Good.mem hI φ κ)).trans ((congrArg _ (h y I hI)).trans
      (sec_trans t κ y hy (Good.mem hI φ κ)).symm)

theorem app_generic_injective {V : Type} [CommRing V] [IsDomain V] (B : Over (Spec (CommRingCat.of V))) [Flat B.hom]
    (U : B.left.Opens) : Function.Injective ((snd (TK V) B).left.app U).hom := by
  have : IsDominant (jK V) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK V)
  exact (pullback.snd (jK V) B.hom).app_injective U

end KunnethDomain


open KunnethDomain ReciprocityTheory.ChartRestriction.G.DVR in
theorem exists_smul_eq_sum_mul_of_isDomain : ∀ (V : Type) [CommRing V] [IsDomain V] (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (Y₁ Y₂ : Over (Spec (CommRingCat.of V))) [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom] [Flat Y₁.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom] [Flat Y₂.hom] (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y₁.left ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂.left ⟶ Z)) (ε₂ : K₂ → ℤ) (v : LB.Sec (LB.LinComb L (K := K₁ ⊕ K₂) (Sum.elim (fun k => (fst Y₁ Y₂).left ≫ φ₁ k) (fun k => (snd Y₁ Y₂).left ≫ φ₂ k)) (Sum.elim ε₁ ε₂))), ∃ (r : V) (_ : r ≠ 0) (n : ℕ) (a : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (b : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)), ∀ (T : Scheme.{0}) (ρ : T ⟶ (Y₁ ⊗ Y₂).left) (z : T) (J), Good L z J → ∑ i, sval (a i) (ρ ≫ (fst Y₁ Y₂).left) z J * sval (b i) (ρ ≫ (snd Y₁ Y₂).left) z J = gs ρ z ⊤ (scal (Y₁ ⊗ Y₂).hom r) * sval v ρ z J := by
  intro V _ _ Z L hL Y₁ Y₂ _ _ _ _ _ _ K₁ K₂ _ _ φ₁ ε₁ φ₂ ε₂ v
  classical
  let G₁ : Over (Spec (CommRingCat.of (FractionRing V))) := Over.mk (fst (TK V) Y₁).left
  let G₂ : Over (Spec (CommRingCat.of (FractionRing V))) := Over.mk (fst (TK V) Y₂).left
  have : QuasiCompact G₁.hom := inferInstanceAs (QuasiCompact (pullback.fst (jK V) Y₁.hom))
  have : IsSeparated G₁.hom := inferInstanceAs (IsSeparated (pullback.fst (jK V) Y₁.hom))
  have : QuasiCompact G₂.hom := inferInstanceAs (QuasiCompact (pullback.fst (jK V) Y₂.hom))
  have : IsSeparated G₂.hom := inferInstanceAs (IsSeparated (pullback.fst (jK V) Y₂.hom))
  have : Flat (Y₁ ⊗ Y₂).hom := inferInstanceAs (Flat (pullback.fst Y₁.hom Y₂.hom ≫ Y₁.hom))
  let p₁ : (G₁ ⊗ G₂).left ⟶ (TK V ⊗ Y₁).left := (fst G₁ G₂).left
  let p₂ : (G₁ ⊗ G₂).left ⟶ (TK V ⊗ Y₂).left := (snd G₁ G₂).left
  have hp : p₁ ≫ (fst (TK V) Y₁).left = p₂ ≫ (fst (TK V) Y₂).left := (Over.w (fst G₁ G₂)).trans (Over.w (snd G₁ G₂)).symm
  have hp' : p₁ ≫ (TK V ⊗ Y₁).hom = p₂ ≫ (TK V ⊗ Y₂).hom := by
    rw [← Over.w (fst (TK V) Y₁), ← Over.w (fst (TK V) Y₂), ← Category.assoc, hp, Category.assoc]
  obtain ⟨g, g₁, g₂⟩ : ∃ g : (G₁ ⊗ G₂).left ⟶ (Y₁ ⊗ Y₂).left, g ≫ (fst Y₁ Y₂).left = p₁ ≫ (snd (TK V) Y₁).left ∧
      g ≫ (snd Y₁ Y₂).left = p₂ ≫ (snd (TK V) Y₂).left :=
    ⟨pullback.lift (p₁ ≫ (snd (TK V) Y₁).left) (p₂ ≫ (snd (TK V) Y₂).left) (by
      rw [Category.assoc, Category.assoc, Over.w, Over.w, hp']), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨h, h₁, h₂⟩ : ∃ h : (TK V ⊗ Y₁ ⊗ Y₂).left ⟶ (G₁ ⊗ G₂).left, h ≫ p₁ = (TK V ◁ fst Y₁ Y₂).left ∧
      h ≫ p₂ = (TK V ◁ snd Y₁ Y₂).left :=
    ⟨pullback.lift (TK V ◁ fst Y₁ Y₂).left (TK V ◁ snd Y₁ Y₂).left (by
      show (TK V ◁ fst Y₁ Y₂).left ≫ (fst (TK V) Y₁).left = (TK V ◁ snd Y₁ Y₂).left ≫ (fst (TK V) Y₂).left
      rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_fst, whiskerLeft_fst]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hg : h ≫ g = (snd (TK V) (Y₁ ⊗ Y₂)).left := by
    apply pullback.hom_ext
    · show (h ≫ g) ≫ (fst Y₁ Y₂).left = _ ≫ (fst Y₁ Y₂).left
      rw [Category.assoc, g₁, ← Category.assoc, h₁, ← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
    · show (h ≫ g) ≫ (snd Y₁ Y₂).left = _ ≫ (snd Y₁ Y₂).left
      rw [Category.assoc, g₂, ← Category.assoc, h₂, ← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  obtain ⟨v', hv'⟩ := exists_sec hL (K' := K₁ ⊕ K₂)
    (φ' := Sum.elim (fun k => p₁ ≫ (snd (TK V) Y₁).left ≫ φ₁ k) (fun k => p₂ ≫ (snd (TK V) Y₂).left ≫ φ₂ k))
    (ε' := Sum.elim ε₁ ε₂) (fun U _ f => Finset.prod_congr rfl (by
      rintro (k | k) _
      · simp only [Sum.elim_inl]
        rw [← Category.assoc, g₁, Category.assoc]
      · simp only [Sum.elim_inr]
        rw [← Category.assoc, g₂, Category.assoc])) (pullSec L _ _ v g)
  obtain ⟨n, a', b', hab⟩ := (GlobalTheory.T.section_lin_comb_fiber_product_separated (FractionRing V) Z L hL G₁ G₂ K₁ K₂
    (fun k => (snd (TK V) Y₁).left ≫ φ₁ k) ε₁ (fun k => (snd (TK V) Y₂).left ≫ φ₂ k) ε₂).1 v'
  choose r hr σ hσ using fun i => exists_sec_of_generic_fibre V Z L hL Y₁ K₁ φ₁ ε₁ (a' i)
  choose s hs τ hτ using fun i => exists_sec_of_generic_fibre V Z L hL Y₂ K₂ φ₂ ε₂ (b' i)
  let c : Fin n → V := fun i => ∏ j ∈ Finset.univ.erase i, r j * s j
  have hc : ∀ i, c i * (r i * s i) = ∏ j, r j * s j := fun i =>
    Finset.prod_erase_mul Finset.univ (fun j => r j * s j) (Finset.mem_univ i)
  refine ⟨∏ j, r j * s j, Finset.prod_ne_zero_iff.2 fun j _ => mul_ne_zero (hr j) (hs j), n,
    fun i => SecOps.secScale (scal Y₁.hom (c i)) (σ i), τ, ?_⟩
  have val_sum : ∀ (T : Scheme.{0}) (ρ : T ⟶ (Y₁ ⊗ Y₂).left) (z : T) (J), Good L z J →
      sval (secSum fun i => mulSec L _ _ _ _
        (pullSec L _ _ (SecOps.secScale (scal Y₁.hom (c i)) (σ i)) (fst Y₁ Y₂).left)
        (pullSec L _ _ (τ i) (snd Y₁ Y₂).left)) ρ z J =
      ∑ i, sval (SecOps.secScale (scal Y₁.hom (c i)) (σ i)) (ρ ≫ (fst Y₁ Y₂).left) z J *
        sval (τ i) (ρ ≫ (snd Y₁ Y₂).left) z J := fun T ρ z J hJ =>
    (sval_sum _ ρ z hJ).trans (Finset.sum_congr rfl fun i _ => (sval_mul _ _ ρ z hJ).trans
      (congrArg₂ (· * ·) (sval_pull _ _ ρ z hJ) (sval_pull _ _ ρ z hJ)))
  have E : (secSum fun i => mulSec L _ _ _ _
        (pullSec L _ _ (SecOps.secScale (scal Y₁.hom (c i)) (σ i)) (fst Y₁ Y₂).left)
        (pullSec L _ _ (τ i) (snd Y₁ Y₂).left)) = SecOps.secScale (scal (Y₁ ⊗ Y₂).hom (∏ j, r j * s j)) v := by
    refine sec_ext_of_app_injective hL _ (app_generic_injective (Y₁ ⊗ Y₂)) fun y J hJ => ?_
    have q₀ : (h ≫ g) ≫ (Y₁ ⊗ Y₂).hom = (h ≫ p₁) ≫ (TK V ⊗ Y₁).hom := by
      rw [hg, h₁, Over.w, Over.w]
    have q₁ : ((h ≫ p₁) ≫ (snd (TK V) Y₁).left) ≫ Y₁.hom = (h ≫ p₁) ≫ (TK V ⊗ Y₁).hom := by
      rw [Category.assoc, Over.w]
    have q₂ : (h ≫ p₂) ≫ (TK V ⊗ Y₂).hom = (h ≫ p₁) ≫ (TK V ⊗ Y₁).hom := by
      rw [Category.assoc, Category.assoc, hp']
    have e₁ : (h ≫ g) ≫ (fst Y₁ Y₂).left = (h ≫ p₁) ≫ (snd (TK V) Y₁).left := by
      rw [Category.assoc, Category.assoc, g₁]
    have e₂ : (h ≫ g) ≫ (snd Y₁ Y₂).left = (h ≫ p₂) ≫ (snd (TK V) Y₂).left := by
      rw [Category.assoc, Category.assoc, g₂]
    have e₃ : sval v (h ≫ g) y J = ∑ i, sval (a' i) (h ≫ p₁) y J * sval (b' i) (h ≫ p₂) y J :=
      (sval_pull v g h y hJ).symm.trans ((hv' _ h y J hJ).symm.trans (hab _ h y J hJ))
    rw [val_sum _ _ y J hJ, sval_scale _ _ _ y hJ, ← hg, e₁, e₂, e₃, gs_scal_eq, q₀, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sval_scale _ _ _ y hJ, hσ i _ _ y J hJ, hτ i _ _ y J hJ, gs_scal_eq, gs_scal_eq, gs_scal_eq, q₁, q₂, ← hc i,
      map_mul, map_mul]
    ring
  intro T ρ z J hJ
  rw [← val_sum T ρ z J hJ, E, sval_scale _ _ _ z hJ]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTermBasis
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamDim

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_class_reps (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : ℕ)
    (hk : 1 ≤ k) : ∃ ρ : (Fin (Module.finrank ℤ X) → Fin k) → X,
      (∀ q q' mu, ρ q + k • mu = ρ q' → q = q') ∧ (∀ β, ∃ q mu, ρ q + k • mu = β) ∧
      ∀ a b : X, k • a = k • b → a = b := by
  let B := (Module.finBasis ℤ X).equivFun
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  refine ⟨fun q => B.symm (fun i => ((q i : ℕ) : ℤ)), fun q q' mu h => ?_, fun β => ?_, fun a b h => ?_⟩
  · funext i
    have e := congrFun (congrArg B h) i
    simp only [map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply, Pi.add_apply, Pi.smul_apply] at e
    rw [nsmul_eq_mul] at e
    have e2 := congrArg (· % (k : ℤ)) e
    simp only [Int.add_mul_emod_self_left] at e2
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (q i).2),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (q' i).2)] at e2
    exact Fin.ext (by exact_mod_cast e2)
  · refine ⟨fun i => ⟨(B β i % k).toNat, ?_⟩, B.symm (fun i => B β i / k), ?_⟩
    · have := Int.emod_lt_of_pos (B β i) hk'
      have := Int.emod_nonneg (B β i) hk'.ne'
      omega
    · apply B.injective
      funext i
      simp only [map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply, Pi.add_apply, Pi.smul_apply]
      rw [nsmul_eq_mul, Int.toNat_of_nonneg (Int.emod_nonneg _ hk'.ne')]
      exact Int.emod_add_mul_ediv _ _
  · apply B.injective
    funext i
    have e := congrFun (congrArg B h) i
    simp only [map_nsmul, Pi.smul_apply, nsmul_eq_mul] at e
    exact mul_left_cancel₀ hk'.ne' e

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
  [Algebra (FractionRing R) F] {k : ℕ}

theorem fam_term_eq (hG : GlobalFnsSt) {s t : Fam D F k} {ρ : D.X} (h : s.s ρ = t.s ρ) (mu : D.X) (j) :
    (s.s (ρ + k • mu)).f j = (t.s (ρ + k • mu)).f j := by
  have hL := D.P.isLB
  obtain ⟨u, hu, hc⟩ := (gen_fe (D := D) (F := F) hG k mu ρ).1
  refine sec_ext_val hL (fun y J hJ => ?_) j
  rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (s.fe mu ρ u hu hc) _ _ y J hJ,
    (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (t.fe mu ρ u hu hc) _ _ y J hJ, h]

theorem sum_smul_f {I : Type} (S : Finset I) (c : I → F) (e : I → Fam D F k) (α : D.X) (j) :
    ((∑ x ∈ S, c x • e x).s α).f j = ∑ x ∈ S, resTop _ (gF D F (c x)) * ((e x).s α).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, zero_f]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, smul_f, ih]

theorem famφ_eq (α : D.X) :
    DegPre.famφ D F α = fun i => (snd (TF (R := R) F) D.P.A).left ≫ DegPre.famφB D α i := by
  funext i
  fin_cases i
  · exact (Category.comp_id _).symm
  · show (padd D.P.A _ _).left = (snd (TF (R := R) F) D.P.A ≫ padd D.P.A _ _).left
    congr 1
    simp only [padd, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
  · show (toUnit (DegPre.BF D F) ≫ D.c α).left = (snd (TF (R := R) F) D.P.A ≫ toUnit _ ≫ D.c α).left
    rw [comp_toUnit_assoc]
  · show (toUnit (DegPre.BF D F) ≫ η[D.P.A]).left = (snd (TF (R := R) F) D.P.A ≫ toUnit _ ≫ η[D.P.A]).left
    rw [comp_toUnit_assoc]

theorem exists_term_basis (hG : GlobalFnsSt) (hP : PolBaseChangeSt) (hT : TwistBaseChangeStatement)
    [IsNoetherianRing R]
    (hW : ∃ W : (Spec (CommRingCat.of R)).Opens, genericPoint (Spec (CommRingCat.of R)) ∈ W ∧ Nonempty (PsiOn D W))
    (hk : 1 ≤ k) (α : D.X) :
    ∃ b : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)),
      ∀ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)),
        ∃! c : Fin (k ^ D.P.g) → F, ∀ j, s.f j = ∑ i, resTop _ (gF D F (c i)) * (b i).f j := by
  let f : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have key : ∀ (t : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)), t = Spec.map (CommRingCat.ofHom f) →
      ∀ φ : Fin 4 → ((Over.mk t ⊗ D.P.A).left ⟶ D.P.A.left),
        φ = (fun i => (snd (Over.mk t) D.P.A).left ≫ DegPre.famφB D α i) →
      ∃ b : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L φ (DegPre.famε k)),
        IsSecBasis (T := Over.mk t) (A := D.P.A) _ b := by
    rintro t rfl φ rfl
    obtain ⟨b, hb⟩ := GlobalTheory.T.exists_twist_basis_off_prime hP hG hT R D hW ⊥ k hk α
    let b' := fun i => DVR.pullSec (L := D.P.L) (DegPre.famφB D α) (DegPre.famε k) (b i)
      (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left
    refine ⟨b', hb F f (fun s hs => ?_) b' (fun i j => rfl)⟩
    refine IsUnit.mk0 _ fun h0 => hs ?_
    have h1 : algebraMap R (FractionRing R) s = 0 := (algebraMap (FractionRing R) F).injective (h0.trans (map_zero _).symm)
    exact (IsFractionRing.to_map_eq_zero_iff (K := FractionRing R)).1 h1
  obtain ⟨b, hb⟩ := key (jFK (R := R) F ≫ jK R) (by
    simp only [jFK, jK, f, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) _ (famφ_eq α)
  refine ⟨b, fun s => ?_⟩
  obtain ⟨r, hr, hu⟩ := hb s
  let e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
  refine ⟨fun i => e (r i), fun j => (hr j).trans (Finset.sum_congr rfl fun i _ => ?_), fun c hc => ?_⟩
  · congr 2
    show _ = (fst (TF (R := R) F) D.P.A).left.appTop.hom (e.symm (e (r i)))
    rw [e.symm_apply_apply]
  · have := hu (fun i => e.symm (c i)) hc
    funext i
    rw [← this]
    exact (e.apply_symm_apply _).symm

theorem finrank_fam : GlobalFnsSt → PolBaseChangeSt → DVR.TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), D.TauBimult → (∃ W : (Spec (CommRingCat.of R)).Opens, genericPoint (Spec (CommRingCat.of R)) ∈ W ∧ Nonempty (PsiOn D W)) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → Module.Finite F (Fam D F k) ∧ Module.finrank F (Fam D F k) = k ^ (D.rank + D.P.g) := by
  intro hG hP hT R _ _ _ D hB hW F _ _ k hk
  classical
  obtain ⟨ρ, hρ, hsurj, hcan⟩ := exists_class_reps D.X k hk
  choose b hb using fun α => exists_term_basis (D := D) (F := F) hG hP hT hW hk α
  choose e he he0 using fun x : (Fin D.rank → Fin k) × Fin (k ^ D.P.g) =>
    UUA.exists_fam_rep (F := F) hG hB k (ρ x.1) (fun a c h => hcan a c (add_left_cancel h)) (b (ρ x.1) x.2)
  have ev : ∀ (c : (Fin D.rank → Fin k) × Fin (k ^ D.P.g) → F) q j,
      ((∑ x, c x • e x).s (ρ q)).f j = ∑ i, resTop _ (gF D F (c (q, i))) * (b (ρ q) i).f j := by
    intro c q j
    rw [sum_smul_f, Fintype.sum_prod_type, Finset.sum_eq_single q]
    · exact Finset.sum_congr rfl fun i _ => by rw [he (q, i)]
    · intro q' _ hq
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [he0 (q', i) (ρ q) (fun mu h => hq (hρ _ _ _ h)) j, mul_zero]
    · intro h; exact absurd (Finset.mem_univ q) h
  have hli : LinearIndependent F e := by
    rw [Fintype.linearIndependent_iff]
    rintro c hc ⟨q, i⟩
    have h1 := (hb (ρ q) SecOps.secZero).unique (y₁ := fun i => c (q, i)) (y₂ := fun _ => 0)
      (fun j => by rw [← ev, hc]; rfl)
      (fun j => by simp only [map_zero, resTop, zero_mul, Finset.sum_const_zero]; rfl)
    exact congrFun h1 i
  have hsp : ⊤ ≤ Submodule.span F (Set.range e) := by
    intro s _
    choose c hc using fun q => (hb (ρ q) (s.s (ρ q))).exists
    refine (Submodule.mem_span_range_iff_exists_fun F).2 ⟨fun x => c x.1 x.2, fam_ext fun β j => ?_⟩
    obtain ⟨q, mu, rfl⟩ := hsurj β
    refine fam_term_eq hG (SecOps.sec_ext fun j' => ?_) mu j
    rw [ev (fun x => c x.1 x.2) q j', hc q j']
  let B := Module.Basis.mk hli hsp
  refine ⟨Module.Finite.of_basis B, ?_⟩
  rw [Module.finrank_eq_card_basis B, pow_add]
  simp

end GlobalTheory.FamDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OLinearIffIsOLinear
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OLinearCompare

open GlobalTheory.TorusCoord

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen :=
  isGen_of_gm _ fun _ _ _ _ _ =>
    (map_one _).trans (Eq.symm ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)))

theorem val₂_axis {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L))
    {T : Over S} {z : T.left} {J} (hJ : Good L z J) (x : T ⟶ A) : val₂ u z J x 1 = 1 := by
  have key := gen_unique' hL (u := LB.pullGen L _ _ u (lift (𝟙 A) (1 : A ⟶ A)).left)
    (u' := LB.oneGen L) (fun U _ h => by
      refine (Fintype.prod_empty _).trans (Eq.symm ((prod_ros f g (𝟙 A) 1 h).trans ?_))
      rw [MonObj.one_comp, _root_.mul_one, _root_.mul_one]
      simp)
    A.hom η[A].left (Over.w η[A]) (globalFns_holds _ _ hA).2 (DVR.pullGen_isGen _ _ _ _ hu _)
    (oneGen_isGen L) (fun y I hI => by
      have := val_corr hI h₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp, val_one] at this
      rw [val_pull hI, val_one, ← Over.comp_left]
      have e : η[A] ≫ lift (𝟙 A) (1 : A ⟶ A) = lift η[A] η[A] := by simp [Hom.one_def]
      rw [e]; exact this) _ x.left z J hJ
  rw [val_pull hJ, val_one, ← Over.comp_left, comp_lift, Category.comp_id, MonObj.comp_one] at key
  exact key

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem val_pull_lift {b b' : D.P.A ⟶ D.P.A}
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A b' b) rosatiε)) (χ : D.X)
    {T Z : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (x : Z ⟶ T) {z : Z.left} {J}
    (hJ : Good D.P.L z J) :
    val (LB.pullGen D.P.L _ _ u (lift (toUnit T ≫ D.c χ) p).left) x.left z J =
      val₂ u z J (toUnit Z ≫ D.c χ) (x ≫ p) := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift, comp_toUnit_assoc]; rfl

end GlobalTheory.OLinearCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkInjective
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionMapInj

theorem qkToAk_injective : Laws → Laws2 → QkToAkInjSt := by
  intro hL hL₂ R _ _ I hR D A G _ _ hG U F _ _ _ n hn p p' x hp hp'
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨hx, H⟩ := hp w₀ hw₀
  obtain ⟨-, H'⟩ := hp' w₀ hw₀
  obtain ⟨θ, hθ, hact⟩ := GlobalTheory.TorsionTheta.exists_theta_acts hL.kerPow _ A F (jFK (R := R) F) n hn x hx
  obtain ⟨w, hw, Hw⟩ := H θ hθ
  obtain ⟨w', hw', Hw'⟩ := H' θ hθ
  obtain ⟨E₁, E₂⟩ := _root_.GlobalTheory.expandsF_total hL hL₂ R I hR D A G hG U F n hn w₀ hw₀
  have key : ∀ s : Fam D.toPre F n, ∃ s' : Fam D.toPre F n,
      PhiRel D.toPre F n p w s s' ∧ PhiRel D.toPre F n p' w' s s' := fun s => by
    obtain ⟨t, ht⟩ := E₁ s
    obtain ⟨t', ht'⟩ := hact t
    obtain ⟨s', hs'⟩ := E₂ t'
    exact ⟨s', Hw t t' s s' ht hs' ht', Hw' t t' s s' ht hs' ht'⟩
  have hB := D.tau_bimult
  obtain ⟨z, hz⟩ := GlobalTheory.lattice_part_congr_of_phiRel hL.globalFns hL₂.secTwist R D.toPre hB F n hn p p' w w' hw hw' key
  obtain ⟨w₂, hw₂, Hs⟩ := GlobalTheory.QkShift.qk_shift hL.globalFns R D.toPre hB F n hn p (GlobalTheory.TorusExt.qkShift hB p z) z
    (GlobalTheory.TorusExt.iota hB F z) rfl (GlobalTheory.TorusExt.isIota_iota hB z) ((GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl) w hw
  have key₂ : ∀ s : Fam D.toPre F n, ∃ s' : Fam D.toPre F n,
      PhiRel D.toPre F n (GlobalTheory.TorusExt.qkShift hB p z) w₂ s s' ∧ PhiRel D.toPre F n p' w' s s' := fun s => by
    obtain ⟨s', h, h'⟩ := key s
    exact ⟨s', Hs s s' h, h'⟩
  have hb := _root_.GlobalTheory.PhiBase.b_eq_of_phiRel hL.globalFns hL₂.secTwist R D.toPre hB F n hn _ p' w₂ w' hw₂ hw' key₂ hz
  have hg := _root_.GlobalTheory.qkPt_g_eq_of_phiRel hL.globalFns hL₂.secTwist R D.toPre hB F n hn _ p' w₂ w' hw₂ hw' key₂ hz hb
  exact (GlobalTheory.TorusExt.equiv_iff hB p p').2 ⟨z, hz, hg.symm⟩

end GlobalTheory.TorsionMapInj
end

