module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassConeParametrization
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0266

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayClassParametrizationExists
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem exists_classParam_sup_eq_top : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 →
      ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F),
        ClassParam 𝔣 𝔞 𝔟 r' y v' ∧ 𝔟 ⊔ 𝔣 = ⊤ := by
  intro F _ _ _ 𝔣 h𝔣 𝔞 h𝔞
  obtain ⟨ι, _, r, v, hdom⟩ := exists_coneDomain F 𝔣 h𝔣
  obtain ⟨𝔟, x₀, hb, hx0, hx1, hxp, hab⟩ := exists_complement h𝔣 h𝔞
  obtain ⟨N, w, hN, hw⟩ := exists_scaled (𝔪 := 𝔟 * 𝔣) (mul_ne_zero hb.1 h𝔣) r v
  have hd := hdom.scale hN (u := fun c i => (w c i : F)) (fun c i => (hw c i).2)
  obtain ⟨J, a, b, c, d, e⟩ := classParam_of_scaled hb.1 hx0 hx1 hxp hab hd
    (fun c i => (Ideal.mul_le_left : 𝔟 * 𝔣 ≤ 𝔟) (hw c i).1)
    (fun c i => (Ideal.mul_le_right : 𝔟 * 𝔣 ≤ 𝔣) (hw c i).1)
  exact ⟨𝔟, J, a, b, c, d, e, hb.2⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayRelAntitoneModulusAndPowMod
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.RayFacts

theorem rayRel_mono_powMod_anti (F : Type) [Field F] [NumberField F] :
    (∀ 𝔣 𝔣' I J : Ideal (𝓞 F), 𝔣' ≤ 𝔣 → RayRel F 𝔣' I J → RayRel F 𝔣 I J) ∧
    (∀ l n m : ℕ, n ≤ m → powMod F l m ≤ powMod F l n) := by
  refine ⟨?_, ?_⟩
  · rintro 𝔣 𝔣' I J hle ⟨a, b, ha, hb, ha1, hb1, hσ, h⟩
    exact ⟨a, b, ha, hb, hle ha1, hle hb1, hσ, h⟩
  · intro l n m hnm
    exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hnm)

end GlobalTheory.CompanionTheory.RayFacts
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningAffinePreimage
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem mem_ker_smul_top_of_one_tmul_eq_zero {A A' M : Type*} [CommRing A] [CommRing A'] [Algebra A A']
    (hs : Function.Surjective (algebraMap A A')) [AddCommGroup M] [Module A M] (x : M)
    (h : (1 : A') ⊗ₜ[A] x = 0) :
    x ∈ (RingHom.ker (algebraMap A A')) • (⊤ : Submodule A M) := by
  have ex : Function.Exact (Submodule.subtype (RingHom.ker (algebraMap A A')))
      (Algebra.linearMap A A') := fun a => by
    constructor
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact b.2
  have hs' : Function.Surjective (Algebra.linearMap A A') := hs
  have ex2 := rTensor_exact M ex hs'
  have h0 : LinearMap.rTensor M (Algebra.linearMap A A') ((1 : A) ⊗ₜ[A] x) = 0 := by
    simpa using h
  obtain ⟨z, hz⟩ := (ex2 _).1 h0
  have key : ∀ z : (RingHom.ker (algebraMap A A')) ⊗[A] M,
      TensorProduct.lid A M (LinearMap.rTensor M
        (Submodule.subtype (RingHom.ker (algebraMap A A'))) z) ∈
        (RingHom.ker (algebraMap A A')) • (⊤ : Submodule A M) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simpa only [map_add (f := _)] using add_mem ha hb
    | tmul a m => simpa using Submodule.smul_mem_smul a.2 Submodule.mem_top
  have := key z
  rw [hz] at this
  simpa using this

theorem cst_comp_spec {X : Scheme.{0}} {R A : Type} [CommRing R] [CommRing A]
    (f : X ⟶ Spec (CommRingCat.of A)) (q : R →+* A) (V : X.Opens) (r : R) :
    cst (f ≫ Spec.map (CommRingCat.ofHom q)) V r = cst f V (q r) := by
  have := appLE_cst (f := f ≫ Spec.map (CommRingCat.ofHom q)) (f' := f) (π := 𝟙 X) (g := q)
    (by simp) (V := V) (V' := V) le_rfl r
  have e : (𝟙 X : X ⟶ X).appLE V V le_rfl = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
    exact X.presheaf.map_id _
  rw [e] at this
  exact this

theorem pull_surjective_ker {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A')
    (hg : Function.Surjective g) {X X' : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of A)}
    {f' : X' ⟶ Spec (CommRingCat.of A')} {π : X' ⟶ X}
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) {M : LB X} (hM : M.IsLB)
    {V : X.Opens} (hV : IsAffineOpen V) :
    Function.Surjective (SecOn.pullLE M π V _ le_rfl) ∧
      ∀ s : SecOnR f M V, SecOn.pullLE M π V _ le_rfl ((SecOnR.of f M V).symm s) = 0 →
        s ∈ (RingHom.ker g) • (⊤ : Submodule A (SecOnR f M V)) := by
  letI := g.toAlgebra
  have hb := SecOnR.baseChangeHom_bijective (R := A) (R' := A') hM H hV rfl
  constructor
  · intro y
    obtain ⟨z, hz⟩ := hb.2 y
    obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective A (SecOnR f M V) A' hg z
    refine ⟨x, ?_⟩
    have h := (SecOnR.baseChangeHom_tmul (R := A) (R' := A') H.w le_rfl 1 x).symm.trans hz
    rw [one_smul] at h
    exact h
  · intro s hs
    refine mem_ker_smul_top_of_one_tmul_eq_zero hg s (hb.1 ?_)
    rw [map_zero, SecOnR.baseChangeHom_tmul, one_smul]
    exact hs

theorem mem_smul_top_of_comp {X : Scheme.{0}} {R A : Type} [CommRing R] [CommRing A]
    (f : X ⟶ Spec (CommRingCat.of A)) (q : R →+* A) (M : LB X) (V : X.Opens) (J : Ideal A)
    (K : Ideal R) (hK : ∀ a ∈ J, ∃ r ∈ K, q r = a) (s : SecOnR f M V)
    (hs : s ∈ J • (⊤ : Submodule A (SecOnR f M V))) :
    SecOnR.of (f ≫ Spec.map (CommRingCat.ofHom q)) M V ((SecOnR.of f M V).symm s) ∈
      K • (⊤ : Submodule R (SecOnR (f ≫ Spec.map (CommRingCat.ofHom q)) M V)) := by
  induction hs using Submodule.smul_induction_on' with
  | smul a ha m _ =>
    obtain ⟨r, hr, rfl⟩ := hK a ha
    have e : SecOnR.of (f ≫ Spec.map (CommRingCat.ofHom q)) M V
        ((SecOnR.of f M V).symm (q r • m)) =
        r • SecOnR.of (f ≫ Spec.map (CommRingCat.ofHom q)) M V ((SecOnR.of f M V).symm m) := by
      rw [SecOnR.smul_def r, cst_comp_spec]
      rfl
    rw [e]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  | add x _ y _ hx hy =>
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem hx hy

theorem redL_surjective_ker : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))) (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V : (Y (e + 1)).left.Opens) (V' : (Y e).left.Opens) (h : β e ⁻¹ᵁ V = V'), IsAffineOpen V → Function.Surjective (redL I Y β hβ L w hL e V V' h.ge) ∧ LinearMap.ker (redL I Y β hβ L w hL e V V' h.ge) = I ^ (e + 1) • ⊤ := by
  intro R _ I Y β hβ L w hL e V V' h hV
  subst h
  have hle : I ^ (e + 1 + 1) ≤ I ^ (e + 1) := Ideal.pow_le_pow_right (Nat.le_succ (e + 1))
  have hq : Function.Surjective (Ideal.Quotient.factor hle) := Ideal.Quotient.factor_surjective hle
  obtain ⟨h1, h2⟩ := pull_surjective_ker (Ideal.Quotient.factor hle) hq (hβ e) (hL (e + 1)).1 hV
  let E := SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
    (hL e).2 (β e ⁻¹ᵁ V))
  have hred (s) : redL I Y β hβ L w hL e V _ le_rfl s =
      E.symm (SecOnR.pull (L (e + 1)) (toR_w I Y β hβ e) V _ le_rfl s) := rfl
  refine ⟨fun y => ?_, le_antisymm (fun s hs => ?_) (Submodule.smul_le.2 fun r hr s _ => ?_)⟩
  · obtain ⟨x, hx⟩ := h1 (E y)
    exact ⟨x, (hred x).trans ((E.symm_apply_eq).2 hx)⟩
  · have hs0 := (E.symm.map_eq_zero_iff).1 ((hred s).symm.trans (LinearMap.mem_ker.1 hs))
    refine mem_smul_top_of_comp (Y (e + 1)).hom (Ideal.Quotient.mk (I ^ (e + 1 + 1))) (L (e + 1)) V
      (RingHom.ker (Ideal.Quotient.factor hle)) (I ^ (e + 1)) (fun a ha => ?_) s (h2 s hs0)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨r, ?_, rfl⟩
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
    exact ha
  · rw [LinearMap.mem_ker, map_smul, SecOnR.smul_def]
    have e0 : cst (toR I Y e) (β e ⁻¹ᵁ V) r = 0 := by
      rw [toR, cst_comp_spec, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
    rw [e0, zero_smul]

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningCechCoverCompatible
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

private theorem rs_rs' {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (z : ↑(X.presheaf.obj (Opposite.op U))) : rs X h₂ (rs X h₁ z) = rs X (h₂.trans h₁) z := by
  simp only [rs]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem congr_secMulOn {X X' : Scheme.{0}} {π : X ⟶ X'} {N : LB X} {N' : LB X'}
    (v : LB.Iso N (N'.pull π)) (hN : N.IsLB) (hN' : N'.IsLB) (hv : v.IsGen) {a b c : ℤ}
    (h : a + b = c) {V : X.Opens} {V' : X'.Opens} (e : V ≤ π ⁻¹ᵁ V')
    (x : SecOn (pw N' a) V') (y : SecOn (pw N' b) V') (s : SecOn (pw N a) V)
    (t : SecOn (pw N b) V)
    (hs : SecOn.congr (isLB_pw hN a) (LB.isLB_pull (isLB_pw hN' a) π) (pullPow v a)
      (pullPow_isGen v a hv) V s = SecOn.pullLE (pw N' a) π V' V e x)
    (ht : SecOn.congr (isLB_pw hN b) (LB.isLB_pull (isLB_pw hN' b) π) (pullPow v b)
      (pullPow_isGen v b hv) V t = SecOn.pullLE (pw N' b) π V' V e y) :
    SecOn.congr (isLB_pw hN c) (LB.isLB_pull (isLB_pw hN' c) π) (pullPow v c)
      (pullPow_isGen v c hv) V (secMulOn h s t) =
      SecOn.pullLE (pw N' c) π V' V e (secMulOn h x y) := by
  subst h
  classical
  have hMc : ((pw N' (a + b)).pull π).IsLB := LB.isLB_pull (isLB_pw hN' (a + b)) π
  have key : ∀ (p : ((pw N' (a + b)).pull π).ι) (q : N.ι) {O : X.Opens}
      (hp : O ≤ V ⊓ ((pw N' (a + b)).pull π).U p)
      (hq : O ≤ V ⊓ (pw N (a + b)).U q) (hpq : O ≤ ((pw N' (a + b)).pull π).U p ⊓ (pw N (a + b)).U q),
      rs X hp (GlobalTheory.LB.coord (SecOn.congr (isLB_pw hN (a + b)) (LB.isLB_pull (isLB_pw hN' (a + b)) π)
        (pullPow v (a + b)) (pullPow_isGen v (a + b) hv) V (secMulOn rfl s t)) p) =
      rs X hp (GlobalTheory.LB.coord (SecOn.pullLE (pw N' (a + b)) π V' V e (secMulOn rfl x y)) p) := by
    intro p q O hp hq hpq
    have ha := SecOn.coord_congr (isLB_pw hN a) (LB.isLB_pull (isLB_pw hN' a) π) (pullPow v a)
      (pullPow_isGen v a hv) s p q hp hq hpq
    have hb := SecOn.coord_congr (isLB_pw hN b) (LB.isLB_pull (isLB_pw hN' b) π) (pullPow v b)
      (pullPow_isGen v b hv) t p q hp hq hpq
    rw [hs, SecOn.coord_pullLE π e x p] at ha
    rw [ht, SecOn.coord_pullLE π e y p] at hb
    rw [SecOn.coord_congr (isLB_pw hN (a + b)) (LB.isLB_pull (isLB_pw hN' (a + b)) π) (pullPow v (a + b))
      (pullPow_isGen v (a + b) hv) _ p q hp hq hpq, SecOn.coord_pullLE π e (secMulOn rfl x y) p,
      coord_secMulOn, coord_secMulOn rfl x y (p PUnit.unit)]
    erw [map_mul, map_mul, map_mul, ha, hb]
    dsimp only [pullPow]
    erw [zpow_add, Units.val_mul, map_mul]
    exact mul_mul_mul_comm _ _ _ _
  have hcov : V ≤ ⨆ a' : ((pw N' (a + b)).pull π).ι × N.ι, V ⊓ ((pw N' (a + b)).pull π).U a'.1 ⊓ N.U a'.2 := by
    intro z hz
    have h1 : z ∈ (⨆ i, ((pw N' (a + b)).pull π).U i) := by rw [hMc.cover]; trivial
    have h2 : z ∈ (⨆ i, N.U i) := by rw [hN.cover]; trivial
    rw [TopologicalSpace.Opens.mem_iSup] at h1 h2 ⊢
    obtain ⟨p, hp⟩ := h1
    obtain ⟨q, hq⟩ := h2
    exact ⟨(p, q), ⟨⟨hz, hp⟩, hq⟩⟩
  refine SecOn.ext_of_cover
    (fun a' : ((pw N' (a + b)).pull π).ι × N.ι => V ⊓ ((pw N' (a + b)).pull π).U a'.1 ⊓ N.U a'.2)
    (fun a' => inf_le_left.trans inf_le_left) hcov ?_
  intro a'
  apply (SecOn.chart hMc a'.1 (inf_le_left.trans inf_le_right)).injective
  rw [SecOn.chart_apply, SecOn.chart_apply, SecOn.coord_restrict, SecOn.coord_restrict, rs_rs', rs_rs']
  exact key a'.1 a'.2 _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)

private theorem secOnR_linEquiv_symm_of {X : Scheme.{0}} {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {L M : LB X} {V : X.Opens} (φ : SecOn L V ≃ₗ[↑(X.presheaf.obj (Opposite.op V))] SecOn M V) (m : SecOn M V) :
    (SecOnR.linEquiv f φ).symm (SecOnR.of f M V m) = SecOnR.of f L V (φ.symm m) := by
  rw [LinearEquiv.symm_apply_eq, SecOnR.linEquiv_of, LinearEquiv.apply_symm_apply]

theorem red_secMulOn : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (hDβ : ∀ e S, D e S ≤ β e ⁻¹ᵁ D (e + 1) S) (a b c : ℤ) (h : a + b = c) (e : ℕ) (S : Finset ι) (x : SecOn (pw (N (e + 1)) a) (D (e + 1) S)) (y : SecOn (pw (N (e + 1)) b) (D (e + 1) S)), red I Y N D β hβ v hN hDβ c e S (SecOnR.of _ _ _ (secMulOn h x y)) = SecOnR.of _ _ _ (secMulOn h ((SecOnR.of _ _ _).symm (red I Y N D β hβ v hN hDβ a e S (SecOnR.of _ _ _ x))) ((SecOnR.of _ _ _).symm (red I Y N D β hβ v hN hDβ b e S (SecOnR.of _ _ _ y)))) := by
  intro R _ I Y β hβ N v hN ι D hDβ a b c h e S x y
  simp only [red, redL, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, SecOnR.pull_of,
    secOnR_linEquiv_symm_of, LinearEquiv.symm_apply_apply]
  refine congrArg (SecOnR.of _ _ _) ?_
  rw [LinearEquiv.symm_apply_eq]
  exact (congr_secMulOn (v e) (hN e).1 (hN (e + 1)).1 (hN e).2 h (hDβ e S) x y _ _
    (LinearEquiv.apply_symm_apply _ _) (LinearEquiv.apply_symm_apply _ _)).symm

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningCechRestrictionCommutes
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem pullLE_oneOn_eq_congr {X Y : Scheme.{0}} {N : LB X} {N' : LB Y} {β : X ⟶ Y}
    (v : LB.Iso N (N'.pull β)) (hL : (pw N 0).IsLB) (hM : ((pw N' 0).pull β).IsLB)
    (hw : (pullPow v 0).IsGen) (V : Y.Opens) (V' : X.Opens) (e : V' ≤ β ⁻¹ᵁ V) :
    SecOn.pullLE (pw N' 0) β V V' e (oneOn N' rfl V) =
      SecOn.congr hL hM (pullPow v 0) hw V' (oneOn N rfl V') := by
  refine GlobalTheory.LB.sec_ext_of_cover hL.cover fun p q => ?_
  have h := SecOn.coord_congr hL hM (pullPow v 0) hw (oneOn N rfl V') p q
    (O := V' ⊓ ((pw N' 0).pull β).U p ⊓ (pw N 0).U q) inf_le_left
    (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ inf_le_right)
  have c1 : GlobalTheory.LB.coord (SecOn.pullLE (pw N' 0) β V V' e (oneOn N' rfl V)) p = 1 := by
    rw [SecOn.coord_pullLE]
    exact map_one _
  have c2 : GlobalTheory.LB.coord (oneOn N (rfl : (0 : ℤ) = 0) V') q = 1 := rfl
  have c3 : (show Γ(X, ((pw N' 0).pull β).U p ⊓ (pw N 0).U q)ˣ from (pullPow v 0).s (p, q)) = 1 :=
    zpow_zero _
  rw [c2, c3] at h
  rw [c1]
  refine Eq.trans ?_ h.symm
  simp

theorem red_oneOn : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (hDβ : ∀ e S, D e S ≤ β e ⁻¹ᵁ D (e + 1) S) (a : ℤ) (h : a = 0) (e : ℕ) (S : Finset ι), red I Y N D β hβ v hN hDβ a e S (SecOnR.of _ _ _ (oneOn (N (e + 1)) h (D (e + 1) S))) = SecOnR.of _ _ _ (oneOn (N e) h (D e S)) := by
  intro R _ I Y β hβ N v hN ι D hDβ a h e S
  subst h
  simp only [red, redL, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_eq, SecOnR.pull_of, SecOnR.linEquiv_of]
  exact congrArg (SecOnR.of _ _ _) (pullLE_oneOn_eq_congr (v e) _ _ _ _ _ _)

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningRestrictionCompatibleOpens
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem redL_restrict : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))) (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V W : (Y (e + 1)).left.Opens) (V' W' : (Y e).left.Opens) (hV : V' ≤ β e ⁻¹ᵁ V) (hW : W' ≤ β e ⁻¹ᵁ W) (h : W ≤ V) (h' : W' ≤ V') (x : SecOnR (toR I Y (e + 1)) (L (e + 1)) V), redL I Y β hβ L w hL e W W' hW (SecOnR.restrict _ _ h x) = SecOnR.restrict _ _ h' (redL I Y β hβ L w hL e V V' hV x) := by
  intro R _ I Y β hβ L w hL e V W V' W' hV hW h h' x
  have key := SecOnR.pull_restrict (M := L (e + 1)) (toR_w I Y β hβ e) h h' hV hW x
  apply (SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
    (hL e).2 W')).injective
  simp only [redL, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [key]
  obtain ⟨y, hy⟩ := (SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
    (hL e).2 V')).surjective (SecOnR.pull (L (e + 1)) (toR_w I Y β hβ e) V V' hV x)
  rw [← hy, LinearEquiv.symm_apply_apply]
  exact (SecOn.congr_restrict (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e) (hL e).2 h' y).symm

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningSectionHomogeneousForm
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace Sp spMap)

namespace GlobalTheory.CompanionTheory.GE

theorem comp_app_eq_zero_iff {X Y Z : Scheme.{0}} (b : X ⟶ Y) [IsIso b] (g : Y ⟶ Z) (U : Z.Opens)
    (s : Γ(Z, U)) : ((b ≫ g).app U).hom s = 0 ↔ (g.app U).hom s = 0 := by
  rw [Scheme.Hom.comp_app]
  have hi : Function.Injective (b.app (g ⁻¹ᵁ U)).hom :=
    (ConcreteCategory.bijective_of_isIso (b.app (g ⁻¹ᵁ U))).1
  change (b.app (g ⁻¹ᵁ U)).hom ((g.app U).hom s) = 0 ↔ _
  exact map_eq_zero_iff _ hi

theorem mem_ker_thickι_iff {R : Type} [CommRing R] (I : Ideal R) (N e : ℕ) (k : Fin (N + 1))
    (s : Γ(PSpace R N, GlobalTheory.ProjSpace.chart R N k)) :
    s ∈ (Scheme.Hom.ker (thickι R I N e)).ideal
        ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩ ↔
      ((GlobalTheory.ProjSpace.baseChange N (Ideal.Quotient.mk (I ^ (e + 1)))).app
        (GlobalTheory.ProjSpace.chart R N k)).hom s = 0 := by
  have h := GlobalTheory.ProjSpace.isPullback_baseChange N (Ideal.Quotient.mk (I ^ (e + 1)))
  have hb : h.isoPullback.hom ≫ thickι R I N e =
      GlobalTheory.ProjSpace.baseChange N (Ideal.Quotient.mk (I ^ (e + 1))) := h.isoPullback_hom_fst
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker, ← hb]
  exact (comp_app_eq_zero_iff h.isoPullback.hom (thickι R I N e) _ s).symm

theorem formOn_eq_zero_iff {R : Type} [CommRing R] {N : ℕ} (k : Fin (N + 1))
    {V : (PSpace R N).Opens} (hV : V = GlobalTheory.ProjSpace.chart R N k) (hle : V ≤ GlobalTheory.ProjSpace.chart R N k)
    {n : ℕ} {f : MvPolynomial (Fin (N + 1)) R} (hf : f.IsHomogeneous n) :
    GlobalTheory.ProjSpace.formOn V k hle n f hf = 0 ↔ f = 0 := by
  subst hV
  rw [← GlobalTheory.ProjSpace.formOn_zero (U := GlobalTheory.ProjSpace.chart R N k) (i := k) (hi := le_rfl) (n := n)]
  exact GlobalTheory.ProjSpace.formOn_chart_inj R N k hf _


open scoped GlobalTheory.ProjSpace in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem exists_formOn_eq {R : Type} [CommRing R] {N : ℕ} (k : Fin (N + 1))
    (s : Γ(PSpace R N, GlobalTheory.ProjSpace.chart R N k)) :
    ∃ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n),
      s = GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n f hf := by
  obtain ⟨p, rfl⟩ := (GlobalTheory.ProjSpace.chartAlgEquiv R N k).surjective s
  obtain ⟨n, f, hf, h⟩ := HomogeneousLocalization.Away.mk_surjective _ (GlobalTheory.ProjSpace.X_mem R N k)
    (GlobalTheory.ProjSpace.polyEquivAway R N k p)
  have hf' : f.IsHomogeneous n := by simpa using hf
  refine ⟨n, f, hf', ?_⟩
  rw [← GlobalTheory.ProjSpace.chartAlgEquiv_dehom R N k hf']
  congr 1
  have h1 := GlobalTheory.ProjSpace.awayToPoly_mk R N k n f hf
  rw [h] at h1
  exact ((GlobalTheory.ProjSpace.polyEquivAway R N k).left_inv p).symm.trans h1

theorem ker_thickι_chart : ∀ {R : Type} [CommRing R] (I : Ideal R) (N e : ℕ) (k : Fin (N + 1)),
    (∀ s ∈ (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩,
      ∃ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
        t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ∧
        s = GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht) ∧
    (∀ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
      t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) →
      GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht ∈
        (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩) := by
  intro R _ I N e k
  have hmem : ∀ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
      GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht ∈
        (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩ ↔
      t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
    intro n t ht
    rw [mem_ker_thickι_iff, GlobalTheory.ProjSpace.baseChange_app_formOn,
      formOn_eq_zero_iff k (GlobalTheory.ProjSpace.baseChange_preimage_chart N _ k), ← RingHom.mem_ker,
      MvPolynomial.ker_map, Ideal.mk_ker]
  refine ⟨fun s hs => ?_, fun n t ht h => (hmem n t ht).2 h⟩
  obtain ⟨n, t, ht, rfl⟩ := exists_formOn_eq k s
  exact ⟨n, t, ht, (hmem n t ht).1 hs, rfl⟩

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningTwistedSectionTransition
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem mul_mul_cancel_of_eq_one {A : Type*} [CommRing A] (a b c : A) (h : b * c = 1) :
    a * b * c = a := by
  rw [mul_assoc, h, mul_one]

theorem mul_mul_cancel_of_eq_one' {A : Type*} [CommRing A] (a b c : A) (h : c * b = 1) :
    a * b * c = a := by
  rw [mul_assoc, mul_comm b, h, mul_one]

theorem mulT_bijective_of_inverse :
    ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℤ) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (e : ℕ) (t : ℤ) (S : Finset ι) (σ : SecOn (pw (N e) d) (D e S)) (y : SecOn (pw (N e) (-d)) (D e S)), secMulOn rfl σ y = oneOn (N e) (add_neg_cancel d) (D e S) → Function.Bijective (mulT I Y N D d e t S σ) := by
  intro R _ I Y β hβ N v hN d ι D e t S σ y h
  have hc : ∀ i : (N e).ι, @HMul.hMul (Γ((Y e).left, D e S ⊓ (N e).U i)) (Γ((Y e).left, D e S ⊓ (N e).U i)) _ _ (GlobalTheory.LB.coord σ i) (GlobalTheory.LB.coord y i) = 1 := by
    intro i
    have := congrArg (fun z : SecOn (pw (N e) (d + -d)) (D e S) =>
      GlobalTheory.LB.coord z (show (pw (N e) (d + -d)).ι from i)) h
    exact this
  let g : Tm I Y N D d e (t + 1) S →ₗ[R] Tm I Y N D d e t S :=
    mulRight (toR I Y e) (show d * (t + 1) + -d = d * t by ring) y
  refine Function.bijective_iff_has_inverse.2 ⟨g, ?_, ?_⟩
  · intro x
    exact GlobalTheory.LB.sec_ext fun (i : (N e).ι) =>
      mul_mul_cancel_of_eq_one (A := Γ((Y e).left, D e S ⊓ (N e).U i)) _ _ _ (hc i)
  · intro x
    exact GlobalTheory.LB.sec_ext fun (i : (N e).ι) =>
      mul_mul_cancel_of_eq_one' (A := Γ((Y e).left, D e S ⊓ (N e).U i)) _ _ _ (hc i)

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

