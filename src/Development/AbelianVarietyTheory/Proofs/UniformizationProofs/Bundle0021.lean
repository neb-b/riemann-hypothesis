module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CorrOfValFieldExtension
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem stalkMap_injective_of_flat' {Y Z : Scheme.{0}} (ρ : Z ⟶ Y) [Flat ρ] (z : Z) :
    Function.Injective (ρ.stalkMap z).hom := by

  let _ := (ρ.stalkMap z).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z) := Flat.stalkMap ρ z
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z)) :=
    (by infer_instance : IsLocalHom (ρ.stalkMap z).hom)
  have : Module.FaithfullyFlat (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z)

theorem corr_of_val_flat_surjective {X Y Z : Scheme.{0}} (ρ : Z ⟶ Y) [Flat ρ] [Surjective ρ] {L : LB X}
    (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)}
    {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : ∀ z J, Good L z J → val t ρ z J = val t' ρ z J) : LB.Gen.Corr L φ ε φ' ε' t t' := by

  have : Epi ρ := Flat.epi_of_flat_of_surjective ρ
  refine corr_of_val hL fun y J hJ => ?_
  obtain ⟨z, rfl⟩ := ρ.surjective y
  obtain ⟨J', hJ', hJJ'⟩ := exists_good L hL z (fun ψ : Y ⟶ X => ρ ≫ ψ) J
    (fun a b hab => congrArg J ((cancel_epi ρ).1 hab)) (fun ψ => by simpa using hJ ψ)
  have hpull : (fun ψ : Y ⟶ X => J' (ρ ≫ ψ)) = J := funext hJJ'
  have e₁ := (values_natural X Y Y Z L K φ ε (𝟙 Y) ρ z J' hJ').2.2.1 t
  have e₂ := (values_natural X Y Y Z L K' φ' ε' (𝟙 Y) ρ z J' hJ').2.2.1 t'
  rw [Category.comp_id, hpull] at e₁ e₂

  apply Units.ext
  apply stalkMap_injective_of_flat' ρ z
  rw [← e₁, ← e₂, h z J' hJ']

theorem corr_of_val_field_extension : ∀ (K₀ F : Type) [Field K₀] [Field F] (f : K₀ →+* F) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Spec (CommRingCat.of K₀) ⟶ X)) (ε : K → ℤ) (φ' : K' → (Spec (CommRingCat.of K₀) ⟶ X)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')), (∀ z J, Good L z J → val t (Spec.map (CommRingCat.ofHom f)) z J = val t' (Spec.map (CommRingCat.ofHom f)) z J) → LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro K₀ F _ _ f X L hL K K' _ _ φ ε φ' ε' t t' h

  have hff : (CommRingCat.ofHom f).hom.FaithfullyFlat := by
    let _ := f.toAlgebra
    show Module.FaithfullyFlat K₀ F
    infer_instance
  obtain ⟨h₁, h₂⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom f)).2 hff
  exact corr_of_val_flat_surjective (Spec.map (CommRingCat.ofHom f)) hL h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubeRelScalarsMemMaximalIdeal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_dvr_fraction_order (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] :
    ∃ o : (FractionRing V)ˣ → ℤ, (∀ x y, o (x * y) = o x + o y) ∧
      (∀ (x y : (FractionRing V)ˣ) (u : Vˣ),
        x.val = algebraMap V (FractionRing V) u.val * y.val → o x = o y) ∧
      ∀ x, 0 < o x ↔ ∃ r ∈ IsLocalRing.maximalIdeal V,
        algebraMap V (FractionRing V) r = x.val := by
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V)
  have hne : ∀ x : (FractionRing V)ˣ, v x.val ≠ 0 := fun x =>
    (Valuation.ne_zero_iff v).mpr x.ne_zero
  refine ⟨fun x => - WithZero.log (v x.val), ?_, ?_, ?_⟩
  · intro x y
    simp only [Units.val_mul, map_mul]
    rw [WithZero.log_mul (hne x) (hne y)]
    ring
  · intro x y u h
    have hu : v (algebraMap V (FractionRing V) u.val) = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
      simp [IsDiscreteValuationRing.maximalIdeal]
    simp only [h, map_mul, hu, _root_.one_mul]
  · intro x
    show 0 < - WithZero.log (v x.val) ↔ _
    rw [neg_pos, WithZero.log_lt_iff_lt_exp (hne x), WithZero.exp_zero]
    constructor
    · intro h
      obtain ⟨r, hr⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h.le
      refine ⟨r, ?_, hr⟩
      rw [← hr] at h
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ r).mp h
    · rintro ⟨r, hr, h⟩
      rw [← h]
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ r).mpr hr

theorem cubeRel_scalars_mem_maximalIdeal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (X : Type) [AddCommGroup X] [Module.Free ℤ X] (a : X → (FractionRing V)ˣ), (∀ x y z, ∃ u : Vˣ, (a (x + y + z) * a x * a y * a z).val = algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + z) * a (y + z)).val) → (∀ x, ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val) → {x | ¬ ∃ r ∈ IsLocalRing.maximalIdeal V, algebraMap V (FractionRing V) r = (a x).val}.Finite → ∀ x, x ≠ 0 → ∃ r ∈ IsLocalRing.maximalIdeal V, algebraMap V (FractionRing V) r = (a x).val := by
  intro V _ _ _ X _ _ a hc he hfin x hx
  obtain ⟨o, hmul, hunit, hpos⟩ := exists_dvr_fraction_order V
  rw [← hpos]
  refine even_quadratic_pos_of_finite_nonpos X (fun x => o (a x)) ?_ ?_ ?_ x hx
  · intro x y z
    obtain ⟨u, hu⟩ := hc x y z
    have := hunit _ _ u hu
    simpa only [hmul] using this
  · intro x
    obtain ⟨u, hu⟩ := he x
    exact hunit _ _ u hu
  · refine hfin.subset ?_
    intro x hx
    show ¬ _
    rw [← hpos]
    exact not_lt.mpr hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSumTmulLinearIndependent
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem exists_sum_tmul_linearIndependent {F M N : Type} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] (t : TensorProduct F M N) :
    ∃ (m : ℕ) (e : Fin m → M) (c : Fin m → N), LinearIndependent F e ∧ t = ∑ k, TensorProduct.tmul F (e k) (c k) := by
  classical
  let B := Module.Basis.ofVectorSpace F M
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_left B t
  let σ := c.support.equivFin.symm
  refine ⟨_, fun k => B (σ k), fun k => c (σ k), ?_, ?_⟩
  · exact B.linearIndependent.comp (fun k => (σ k).val) (Subtype.val_injective.comp σ.injective)
  · rw [← hc, Finsupp.sum, ← Finset.sum_coe_sort]
    exact (Equiv.sum_comp σ (fun i => TensorProduct.tmul F (B i) (c i))).symm

section
variable {F : Type} [CommRing F] {Z Y T : Scheme.{0}} {L : LB Z} (p : Y ⟶ Spec (CommRingCat.of F))
  {K : Type} [Fintype K] (φ : K → (Y ⟶ Z)) (ε : K → ℤ)

noncomputable def svalAddHom (r : T ⟶ Y) (z : T) {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) :
    SecMod p (LB.LinComb L φ ε) →+ T.presheaf.stalk z :=
  AddMonoidHom.mk' (fun s => sval s.sec r z J) (fun _ _ => gs_add r z _ (hJ.mem φ r) _ _)

theorem svalAddHom_smul (r : T ⟶ Y) (z : T) {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) (c : F)
    (s : SecMod p (LB.LinComb L φ ε)) :
    svalAddHom p φ ε r z hJ (c • s) =
      gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * svalAddHom p φ ε r z hJ s :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _)
    ((gs_res r z le_top (hJ.mem φ r) _).trans (gs_pull r p z ⊤ trivial _)))

noncomputable def secCompAddHom (N : LB Y) (j : N.ι) : SecMod p N →+ Γ(Y, N.U j) :=
  AddMonoidHom.mk' (fun s => s.sec.f j) (fun _ _ => rfl)

end

theorem tensor_sections_eq_zero_iff : ∀ (F : Type) [Field F] (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (Y₁ Y₂ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec (CommRingCat.of F)) (p₂ : Y₂ ⟶ Spec (CommRingCat.of F)) [QuasiCompact p₁] [IsSeparated p₁] [QuasiCompact p₂] [IsSeparated p₂] (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y₁ ⟶ Z)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y₂ ⟶ Z)) (ε₂ : K₂ → ℤ) (n : ℕ) (a : Fin n → SecMod p₁ (LB.LinComb L φ₁ ε₁)) (b : Fin n → SecMod p₂ (LB.LinComb L φ₂ ε₂)), (∑ i, TensorProduct.tmul F (a i) (b i) = 0) ↔ ∀ (T : Scheme.{0}) (r₁ : T ⟶ Y₁) (r₂ : T ⟶ Y₂), r₁ ≫ p₁ = r₂ ≫ p₂ → ∀ (z : T) (J), Good L z J → ∑ i, sval (a i).sec r₁ z J * sval (b i).sec r₂ z J = 0 := by
  intro F _ Z L hL Y₁ Y₂ p₁ p₂ _ _ _ _ K₁ K₂ _ _ φ₁ ε₁ φ₂ ε₂ n a b
  have key : ∀ (T : Scheme.{0}) (r₁ : T ⟶ Y₁) (r₂ : T ⟶ Y₂), r₁ ≫ p₁ = r₂ ≫ p₂ → ∀ (z : T) (J), Good L z J →
      ∃ Φ : TensorProduct F (SecMod p₁ (LB.LinComb L φ₁ ε₁)) (SecMod p₂ (LB.LinComb L φ₂ ε₂)) →+ T.presheaf.stalk z,
        ∀ s t, Φ (TensorProduct.tmul F s t) = sval s.sec r₁ z J * sval t.sec r₂ z J := by
    intro T r₁ r₂ h z J hJ
    refine ⟨TensorProduct.liftAddHom
      ((AddMonoidHom.mul.compl₂ (svalAddHom p₂ φ₂ ε₂ r₂ z hJ)).comp (svalAddHom p₁ φ₁ ε₁ r₁ z hJ)) ?_, fun s t => rfl⟩
    intro c s t
    change svalAddHom p₁ φ₁ ε₁ r₁ z hJ (c • s) * svalAddHom p₂ φ₂ ε₂ r₂ z hJ t =
      svalAddHom p₁ φ₁ ε₁ r₁ z hJ s * svalAddHom p₂ φ₂ ε₂ r₂ z hJ (c • t)
    rw [svalAddHom_smul, svalAddHom_smul, h]
    ring
  constructor
  · intro h0 T r₁ r₂ h z J hJ
    obtain ⟨Φ, hΦ⟩ := key T r₁ r₂ h z J hJ
    have := congrArg Φ h0
    rwa [map_sum, map_zero, Finset.sum_congr rfl (fun i _ => hΦ (a i) (b i))] at this
  · intro H
    obtain ⟨m, e, c, he, ht⟩ := exists_sum_tmul_linearIndependent (∑ i, TensorProduct.tmul F (a i) (b i))
    have : QuasiCompact (Over.mk p₁).hom := ‹QuasiCompact p₁›
    have : IsSeparated (Over.mk p₁).hom := ‹IsSeparated p₁›
    have : QuasiCompact (Over.mk p₂).hom := ‹QuasiCompact p₂›
    have : IsSeparated (Over.mk p₂).hom := ‹IsSeparated p₂›
    have hc := (GlobalTheory.T.section_lin_comb_fiber_product_separated F Z L hL (Over.mk p₁) (Over.mk p₂) K₁ K₂ φ₁ ε₁ φ₂ ε₂).2 m
      (fun k => (e k).sec) (fun k => (c k).sec) (fun d hd => by
        have h1 : ∑ k, d k • e k = 0 := DVR.SecOps.sec_ext fun j =>
          (map_sum (secCompAddHom p₁ _ j) _ _).trans (hd j)
        exact funext (Fintype.linearIndependent_iff.1 he d h1)) (fun z J hJ => by
        have w : (fst (Over.mk p₁) (Over.mk p₂)).left ≫ p₁ = (snd (Over.mk p₁) (Over.mk p₂)).left ≫ p₂ :=
          (Over.w (fst (Over.mk p₁) (Over.mk p₂))).trans (Over.w (snd (Over.mk p₁) (Over.mk p₂))).symm
        obtain ⟨Φ, hΦ⟩ := key _ _ _ w z J hJ
        have h2 := congrArg Φ ht
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_sum, Finset.sum_congr rfl (fun i _ => hΦ (a i) (b i)),
          Finset.sum_congr rfl (fun i _ => hΦ (e i) (c i))] at h2
        exact h2.symm.trans (H _ _ _ w z J hJ))
    rw [ht]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : c k = 0 := DVR.SecOps.sec_ext fun j => hc k j
    rw [this, TensorProduct.tmul_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtIffStalks
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem gs_res_global_scal_eq_cst {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    (q : Z ⟶ Y) (z : Z) (V : Y.Opens) (hz : q z ∈ V) (c : R) :
    gs q z V (resTop V (scal p c)) = cst (q ≫ p) z c := by
  unfold resTop
  rw [gs_res q z le_top hz]
  unfold scal cst
  exact gs_pull q p z ⊤ trivial _

theorem gs_of_eq_sum_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    (q : Z ⟶ Y) (z : Z) (V : Y.Opens) (hz : q z ∈ V) {n : ℕ} (c : Fin n → R) {a : Γ(Y, V)} {b : Fin n → Γ(Y, V)}
    (h : a = ∑ i, resTop V (scal p (c i)) * b i) :
    gs q z V a = ∑ i, cst (q ≫ p) z (c i) * gs q z V (b i) := by
  subst h
  rw [gs_fsum q z V hz]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul q z V hz, gs_res_global_scal_eq_cst p q z V hz]

theorem expandsAt_iff_stalks {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) :
    U.ExpandsAt e k σ f ↔ ∃ S : Finset D.toPre.X, ∀ (y : (thickObj R I e G).left) (J), Good D.toPre.P.L y J →
      (∀ α ∉ S, sval (f α) (pGl U e) y J = 0) ∧ ∀ jL, (fGl I G e) y ∈ U.LG.L.U jL →
        (wv U e (𝟙 _) y (J (pGl U e)) jL ^ k).val * sv U k σ (fGl I G e) y jL =
          ∑ α ∈ S, sval (f α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val := by
  constructor
  · intro h
    obtain ⟨S, hS⟩ := expandsAt_val U e k σ f h
    refine ⟨S, fun y J hJ => ?_⟩
    have hy := hS _ (𝟙 _) y J hJ
    simp only [Category.id_comp] at hy
    exact hy
  · rintro ⟨S, hS⟩
    exact expandsAt_of_val U e k σ f S hS

theorem expandsAt_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k e n : ℕ) (c : Fin n → R) (σ : Fin n → LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f : Fin n → ∀ α, D.toPre.SecB k α) (σ₀ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f₀ : ∀ α, D.toPre.SecB k α), (∀ i, U.ExpandsAt e k (σ i) (f i)) → (∀ j, σ₀.f j = ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j) → (∀ α j, (f₀ α).f j = ∑ i, resTop _ (scal D.toPre.P.A.hom (c i)) * (f i α).f j) → U.ExpandsAt e k σ₀ f₀ := by
  intro R _ _ I D A G _ _ U k e n c σ f σ₀ f₀ hE hσ hf
  classical
  have hE' := fun i => (expandsAt_iff_stalks U e k (σ i) (f i)).1 (hE i)
  choose S hS using hE'
  refine (expandsAt_iff_stalks U e k σ₀ f₀).2 ⟨Finset.univ.biUnion S, fun y J hJ => ?_⟩
  have hc : pGl U e ≫ D.toPre.P.A.hom = fGl I G e ≫ G.hom := (Over.w _).trans (Over.w _).symm
  have key₀ : ∀ α, sval (f₀ α) (pGl U e) y J =
      ∑ i, cst (pGl U e ≫ D.toPre.P.A.hom) y (c i) * sval (f i α) (pGl U e) y J := fun α =>
    gs_of_eq_sum_scal D.toPre.P.A.hom (pGl U e) y _ (Good.mem hJ _ _) c (hf α _)
  refine ⟨fun α hα => ?_, fun jL hjL => ?_⟩
  · rw [key₀ α]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [(hS i y J hJ).1 α (fun h => hα (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, h⟩)), mul_zero]
  · have hmem : fGl I G e y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL) :=
      Set.mem_iInter.2 fun _ => hjL
    have keyσ : sv U k σ₀ (fGl I G e) y jL =
        ∑ i, cst (fGl I G e ≫ G.hom) y (c i) * sv U k (σ i) (fGl I G e) y jL :=
      gs_of_eq_sum_scal G.hom (fGl I G e) y _ hmem c (hσ _)
    have hR : ∑ α ∈ Finset.univ.biUnion S, sval (f₀ α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val =
        ∑ i, ∑ α ∈ Finset.univ.biUnion S,
          cst (fGl I G e ≫ G.hom) y (c i) * sval (f i α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [key₀ α, Finset.sum_mul, hc]
    rw [hR, keyσ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_left_comm, (hS i y J hJ).2 jL hjL,
      Finset.sum_subset (Finset.subset_biUnion_of_mem S (Finset.mem_univ i))
        (fun α _ hα => by rw [(hS i y J hJ).1 α hα, zero_mul]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [_root_.mul_assoc]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTransport
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ExpTrans

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

section Generic

variable {X X' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

def om (w : LB.Iso L' (L.pull F)) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (ψ : Z ⟶ X') :
    (Z.presheaf.stalk z)ˣ := gw w ψ z (J (ψ ≫ F)) (J' ψ)

variable (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {Y Y' : Scheme.{0}} (φ' : K → (Y' ⟶ X'))
  (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)

theorem sec_val (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L' φ' ε))
    (r : Z ⟶ Y') (z : Z)
    (H : ∀ (p : K → L.ι) (q : K → L'.ι), (∀ κ, F (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ h) z (LB.wchart L φ p) (s.f p) =
        (∏ κ, gw w (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ' q) (s'.f q))
    {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    sval s (r ≫ h) z J = (∏ κ, om w z J J' (r ≫ φ' κ) ^ ε κ).val * sval s' r z J' := by
  rw [sval_of s (r ≫ h) z J (fun κ => J ((r ≫ φ' κ) ≫ F))
    (fun κ => by rw [Category.assoc, Category.assoc, hc])]
  exact H _ (fun κ => J' (r ≫ φ' κ)) (fun κ => hJ ((r ≫ φ' κ) ≫ F)) (fun κ => hJ' (r ≫ φ' κ))

theorem gen_val (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L' φ' ε))
    (H : PMaps w φ' φ ε t' t h) (z : Y') {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    val t h z J = (∏ κ, om w z J J' (φ' κ) ^ ε κ) * val t' (𝟙 _) z J' := by
  have := H _ (𝟙 _) z (fun κ => J (φ' κ ≫ F)) (fun κ => J' (φ' κ)) (fun κ => hJ (φ' κ ≫ F)) (fun κ => hJ' (φ' κ))
  simp only [Category.id_comp] at this
  rw [val_of t h z J (fun κ => J (φ' κ ≫ F)) (fun κ => by rw [hc]),
    val_of t' (𝟙 _) z J' (fun κ => J' (φ' κ)) (fun κ => by rw [Category.id_comp])]
  exact this

end Generic

theorem prod_fam {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)
    {M : Type} [CommGroup M] (ω : ((thickObj R I e G).left ⟶ D.toPre.P.A.left) → M) (α : D.toPre.X) :
    (∏ a, ω (pGl U e ≫ D.toPre.famφB α a) ^ DegPre.famε k a) * ∏ a, ω (Oφl U e α a) ^ Oinvε a =
      ω (pGl U e) ^ k := by
  have a₀ : pGl U e ≫ D.toPre.famφB α 0 = pGl U e := Category.comp_id _
  have a₁ : pGl U e ≫ D.toPre.famφB α 1 = Oφl U e α 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul (U.gt e).pG (𝟙 _) (cP D.toPre _ α)).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D.toPre _ α)))
  have a₂ : pGl U e ≫ D.toPre.famφB α 2 = Oφl U e α 1 :=
    congrArg (fun z => z.left) (comp_cP D.toPre (U.gt e).pG α)
  have a₃ : pGl U e ≫ D.toPre.famφB α 3 = Oφl U e α 3 :=
    congrArg (fun z : _ ⟶ D.toPre.P.A => z.left) (MonObj.comp_one (M := D.toPre.P.A) (U.gt e).pG)
  have a₄ : Oφl U e α 2 = pGl U e := rfl
  rw [Fin.prod_univ_four, Fin.prod_univ_four, a₀, a₁, a₂, a₃, a₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, DegPre.famε, Oinvε, Matrix.cons_val]
  module

end GlobalTheory.ExpTrans

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans in
set_option maxHeartbeats 1600000 in
theorem expandsAt_transport : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (D : DegData R I) (D' : DegData R' I') (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I D A G) (U' : UnifPre I' D' A' G') (Φ : D'.toPre.P.A.left ⟶ D.toPre.P.A.left) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ)) (xe : D'.toPre.X ≃+ D.toPre.X) (Ψ : G'.left ⟶ G.left) (wL : LB.Iso U'.LG.L (U.LG.L.pull Ψ)), w.IsGen → wL.IsGen → (∀ x κ, D'.toPre.famφB x κ ≫ Φ = Φ ≫ D.toPre.famφB (xe x) κ) → ∀ (e e' k : ℕ) (h : (thickObj R' I' e' G').left ⟶ (thickObj R I e G).left), (h ≫ (fstG I e G).left = (fstG I' e' G').left ≫ Ψ ∧ ((U'.gt e').pG.left ≫ Φ = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e').pG x κ ≫ Φ = h ≫ D.toPre.Oφ (U.gt e).pG (xe x) κ) ∧ Geo.Tor.PMaps w (D'.toPre.Oφ (U'.gt e').pG x) (D.toPre.Oφ (U.gt e).pG (xe x)) Oinvε ((U'.gt e').t x) ((U.gt e).t (xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e' G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (Φ) ((U'.gt e').pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e').pG.left (r z) ∈ D'.toPre.P.L.U jM' → (Ψ) ((fstG I' e' G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e' G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw w (r ≫ (U'.gt e').pG.left) z jM jM' * Geo.Tor.gw (U'.w e') r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e' G').left) z jL jL')) → ∀ (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (σ' : LB.Sec (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G'.left) (fun _ => (k : ℤ)))) (f : ∀ α, D.toPre.SecB k α) (f' : ∀ α, D'.toPre.SecB k α), (∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (p : Fin 1 → U.LG.L.ι) (q : Fin 1 → U'.LG.L.ι), (∀ κ, (Ψ) ((fun _ : Fin 1 => 𝟙 G'.left) κ (r z)) ∈ U.LG.L.U (p κ)) → (∀ κ, (fun _ : Fin 1 => 𝟙 G'.left) κ (r z) ∈ U'.LG.L.U (q κ)) → Geo.Tor.gs (r ≫ Ψ) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) p) ((σ).f p) = (∏ κ, Geo.Tor.gw wL (r ≫ (fun _ : Fin 1 => 𝟙 G'.left) κ) z (p κ) (q κ) ^ (fun _ : Fin 1 => (k : ℤ)) κ).val * Geo.Tor.gs r z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) q) ((σ').f q)) → (∀ x : D'.toPre.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.toPre.P.A.left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.toPre.P.L.ι), (∀ κ, (Φ) ((D'.toPre.famφB x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (D'.toPre.famφB x) κ (r z) ∈ D'.toPre.P.L.U (q κ)) → Geo.Tor.gs (r ≫ Φ) z (LB.wchart D.toPre.P.L (D.toPre.famφB (xe x)) p) ((f (xe x)).f p) = (∏ κ, Geo.Tor.gw w (r ≫ (D'.toPre.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.toPre.P.L (D'.toPre.famφB x) q) ((f' x).f q))) → U.ExpandsAt e k σ f → U'.ExpandsAt e' k σ' f' := by
  intro R R' _ _ _ _ I I' D D' A A' G _ _ G' _ _ U U' Φ w xe Ψ wL _ _ hφ e e' k h ⟨hG, ⟨hq, hO⟩, hW⟩ σ σ' f f' hσ hf hE
  classical
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f hE
  refine expandsAt_of_val U' e' k σ' f' (S.map xe.symm.toEquiv.toEmbedding) fun y J' hJ' => ?_
  choose J hJ using fun ψ : (thickObj R' I' e' G').left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  have hq : pGl U' e' ≫ Φ = h ≫ pGl U e := hq
  have hG : h ≫ fGl I G e = fGl I' G' e' ≫ Ψ := hG
  have hF : ∀ α', sval (f (xe α')) (h ≫ pGl U e) y J =
      (∏ a, om w y J J' (pGl U' e' ≫ D'.toPre.famφB α' a) ^ DegPre.famε k a).val * sval (f' α') (pGl U' e') y J' := by
    intro α'
    rw [← hq]
    exact sec_val w _ _ _ Φ (hφ α') (f (xe α')) (f' α') (pGl U' e') y (hf α' _ (pGl U' e') y) hJ hJ'
  have hT : ∀ α', val (tG U e (xe α')) h y J =
      (∏ a, om w y J J' (Oφl U' e' α' a) ^ Oinvε a) * val (tG U' e' α') (𝟙 _) y J' := fun α' =>
    gen_val w (Oφl U' e' α') (Oφl U e (xe α')) Oinvε h (hO α').1 (tG U e (xe α')) (tG U' e' α') (hO α').2 y hJ hJ'
  have hω := prod_fam U' e' k (om w y J J')
  refine ⟨fun α' hα => ?_, fun jL' hL' => ?_⟩
  · have hi : xe α' ∉ S := fun hc => hα (Finset.mem_map.2 ⟨xe α', hc, xe.symm_apply_apply α'⟩)
    exact (Units.mul_right_eq_zero _).1 ((hF α').symm.trans ((hS _ h y J hJ).1 _ hi))
  · obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB (Ψ (fGl I' G' e' y))
    have hL₁ : fGl I G e (h y) ∈ U.LG.L.U jL := (congrArg (fun g => g y ∈ U.LG.L.U jL) hG).mpr hL
    have W' : om w y J J' (pGl U' e') * wv U' e' (𝟙 _) y (J' (pGl U' e')) jL' =
        wv U e h y (J (h ≫ pGl U e)) jL * gw wL (fGl I' G' e') y jL jL' := by
      have := hW _ (𝟙 _) y (J (pGl U' e' ≫ Φ)) (J' (pGl U' e')) jL jL' (hJ (pGl U' e' ≫ Φ)) (hJ' (pGl U' e')) hL hL'
      simp only [Category.id_comp] at this
      rw [← hq]
      exact this
    have Sg : sv U k σ (h ≫ fGl I G e) y jL =
        (gw wL (fGl I' G' e') y jL jL' ^ k).val * sv U' k σ' (fGl I' G' e') y jL' := by
      have := hσ _ (fGl I' G' e') y (fun _ => jL) (fun _ => jL') (fun _ => hL) (fun _ => hL')
      simp only [Category.comp_id, Fin.prod_univ_one, zpow_natCast] at this
      rw [hG]
      exact this
    refine (om w y J J' (pGl U' e') ^ k).mul_right_inj.1 ?_
    rw [← _root_.mul_assoc, ← Units.val_mul, ← mul_pow, W', mul_pow, Units.val_mul, _root_.mul_assoc, ← Sg,
      (hS _ h y J hJ).2 jL hL₁, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    obtain ⟨α', rfl⟩ := xe.surjective x
    have e₀ : xe.symm.toEquiv.toEmbedding (xe α') = α' := xe.symm_apply_apply α'
    rw [e₀, hF α', hT α', ← hω α', Units.val_mul, Units.val_mul, _root_.mul_mul_mul_comm]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelationOfFiniteLevels
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem relation_of_finite_levels : ∀ (R : Type) [CommRing R] (I : Ideal R) (T B : Over (Spec (CommRingCat.of R))) [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] [GrpObj B] [Smooth B.hom] [GeometricallyConnected B.hom], (∀ r ∈ I, scal T.hom r ∈ Ideal.jacobson (⊥ : Ideal Γ(T.left, ⊤))) → ∀ (X Y₂ : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂ ⟶ X)) (ε : K → ℤ) (φ' : K' → ((T ⊗ B).left ⟶ X)) (ε' : K' → ℤ) (φu : K'' → ((T ⊗ B).left ⟶ X)) (εu : K'' → ℤ) (τ : (T ⊗ B).left ⟶ Y₂) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ((T ⊗ B).left, ⊤)), u.IsGen → FormEq φ' ε' (Sum.elim (fun k => τ ≫ φ k) φu) (Sum.elim ε εu) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ (T ⊗ B).hom) → (∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval s' r z J = gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval s' r z J = gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val)) := by
  intro R _ I T B _ _ _ _ _ hI X Y₂ L hL K K' K'' _ _ _ φ ε φ' ε' φu εu τ s s' u c c' hu hF h Z r z J hJ
  obtain ⟨d, hd⟩ := exists_sec_relation_defect _ X Y₂ L hL K K' K'' φ ε φ' ε' φu εu τ s s' u c c' hu hF
  have h0 := sec_eq_zero_of_sval_finite_level R I T B hI X L hL K' φ' ε' d (fun e Z r hr z J hJ => by
    rw [hd Z r z J hJ, h e Z r hr z J hJ, sub_self])
  rw [← sub_eq_zero, ← hd Z r z J hJ]
  exact (congrArg (gs r z _) (h0 _)).trans ((gs_eq r z _ (hJ.mem φ' r) _).trans ((congrArg _ (map_zero _)).trans (map_zero _)))

end GlobalTheory
end

