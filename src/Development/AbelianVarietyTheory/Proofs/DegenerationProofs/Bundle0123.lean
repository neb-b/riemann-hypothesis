module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSecOfLocal
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIntegralRatios
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RatioExt

open GlobalTheory.SecRingIso GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem corresp_refl {X Z : Scheme.{0}} {L : LB X} {φ ψ : Z ⟶ X}
    (hc : ∀ N : ℕ, 4 ≤ N → ∀ x : X, ∃ s : H0 L N, x ∈ nonzeroLocus s)
    (h : ∀ n : ℕ, 1 ≤ n → ∀ (a b : H0 L n) (z : Z) (j j' : Fin 1 → L.ι), φ z ∈ ch L j → ψ z ∈ ch L j' →
      sv φ z a j * sv ψ z b j' = sv φ z b j * sv ψ z a j') :
    Corresp (L := L) (L' := L) (fun _ _ => Equiv.refl _) φ ψ := by
  intro n hn a b z
  refine ⟨?_, fun j j' _ hj hj' => h n hn a b z j j' hj hj'⟩
  have hk : 1 ≤ n * (3 + 1) := by omega
  obtain ⟨d, hd, -⟩ := presMul_refl.exists_pow hn b 3 _ hk rfl
  obtain ⟨c, hcφ⟩ := hc (n * (3 + 1)) (by omega) (φ z)
  obtain ⟨c', hcψ⟩ := hc (n * (3 + 1)) (by omega) (ψ z)
  obtain ⟨j, hj⟩ := exists_ch hcφ
  obtain ⟨j', hj'⟩ := exists_ch hcψ
  show φ z ∈ nonzeroLocus b ↔ ψ z ∈ nonzeroLocus b
  rw [mem_iff b φ z hj, mem_iff b ψ z hj']
  constructor
  · intro hb
    have e := h _ hk d c' z j j' hj hj'
    rw [sv_pow hd φ z hj, sv_pow hd ψ z hj'] at e
    have u := (hb.pow (3 + 1)).mul ((mem_iff c' ψ z hj').1 hcψ)
    rw [e] at u
    exact isUnit_pow_succ_iff.1 (isUnit_of_mul_isUnit_right u)
  · intro hb
    have e := h _ hk c d z j j' hj hj'
    rw [sv_pow hd φ z hj, sv_pow hd ψ z hj'] at e
    have u := ((mem_iff c φ z hj).1 hcφ).mul (hb.pow (3 + 1))
    rw [e] at u
    exact isUnit_pow_succ_iff.1 (isUnit_of_mul_isUnit_left u)

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G]

theorem exists_integral (U : Unif I D A G)
    {w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))} (hw : w.IsGen)
    {n : ℕ} (hn : 1 ≤ n) (a : H0 A.L n) : ∃ (r : R) (σ : H0 U.LG.L n), r ≠ 0 ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ ((Over.pullback (jK R)).obj G).left) (z : Z) (i : U.LG.L.ι) (j : A.L.ι),
        (f ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U i → (f ≫ U.gen.hom.left) z ∈ A.L.U j →
        powVal σ (f ≫ pullback.fst G.hom (jK R)) z i =
          cst ((f ≫ pullback.snd G.hom (jK R)) ≫ jK R) z r *
            ((isoVal w f z i j ^ (n : ℤ)).val * powVal a (f ≫ U.gen.hom.left) z j) := by
  obtain ⟨s, hs⟩ := exists_move A.isLB U.LG.isLB hw (𝟙 _) (n : ℤ) (g₁ := 𝟙 A.A.left) U.gen.hom.left
    ((Category.comp_id _).trans (Category.id_comp _).symm) (g₂ := pullback.fst G.hom (jK R))
    (Category.id_comp _).symm a
  obtain ⟨F, ⟨r, hr, σ, -, h₁, -⟩, -⟩ := (U.expand n hn).1 s
  refine ⟨r, σ, hr, fun Z f z i j hi hj => ?_⟩
  obtain ⟨J, hJ, e⟩ := exists_good U.LG.L U.LG.isLB z (fun _ : Unit => f ≫ pullback.fst G.hom (jK R))
    (fun _ => i) (fun _ _ _ => rfl) (fun _ => hi)
  have e₁ := ExpInt.secScal_sval h₁ f z hJ
  rw [sval_eq_powVal, sval_eq_powVal, Category.comp_id, e (), ExpInt.gs_scal, hs Z f z i j hi hj,
    Category.comp_id, ← Category.assoc] at e₁
  exact e₁

end GlobalTheory.RatioExt

namespace GlobalTheory


open GlobalTheory.SecRingIso GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.RatioExt in
theorem hom_ext_of_integral_ratios : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (P : ∀ k : ℕ, H0 U.LG.L k → Prop), (∀ k : ℕ, 1 ≤ k → ∀ σ₀ : H0 U.LG.L k, ∃ (c : R) (σ : H0 U.LG.L k), c ≠ 0 ∧ (∀ i, σ.f i = resTop _ (scal G.hom c) * σ₀.f i) ∧ P k σ) → ∀ (Z : Scheme.{0}) (f₁ f₂ : Z ⟶ ((Over.pullback (jK R)).obj G).left), f₁ ≫ pullback.snd G.hom (jK R) = f₂ ≫ pullback.snd G.hom (jK R) → (∀ z : Z, ∃ i₁ i₂ : U.LG.L.ι, (f₁ ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U i₁ ∧ (f₂ ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U i₂ ∧ ∀ k : ℕ, 1 ≤ k → ∀ σ τ : H0 U.LG.L k, P k σ → P k τ → gs (f₁ ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₁)) (σ.f (fun _ => i₁)) * gs (f₂ ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₂)) (τ.f (fun _ => i₂)) = gs (f₁ ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₁)) (τ.f (fun _ => i₁)) * gs (f₂ ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₂)) (σ.f (fun _ => i₂))) → f₁ = f₂ := by
  intro hL R _ _ I D A G _ _ U P hP Z f₁ f₂ hK h
  obtain ⟨w, hw⟩ := U.ext
  have key : ∀ n : ℕ, 1 ≤ n → ∀ a : H0 A.L n, ∃ (r : R) (σ : H0 U.LG.L n), r ≠ 0 ∧ P n σ ∧
      ∀ (f : Z ⟶ ((Over.pullback (jK R)).obj G).left) (z : Z) (i : U.LG.L.ι) (j : Fin 1 → A.L.ι),
        (f ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U i → (f ≫ U.gen.hom.left) z ∈ ch A.L j →
        powVal σ (f ≫ pullback.fst G.hom (jK R)) z i =
          cst ((f ≫ pullback.snd G.hom (jK R)) ≫ jK R) z r *
            ((isoVal w f z i (j 0) ^ (n : ℤ)).val * sv (f ≫ U.gen.hom.left) z a j) := fun n hn a => by
    obtain ⟨r, σ₀, hr, H⟩ := exists_integral U hw hn a
    obtain ⟨c, σ, hc, hσ, hPσ⟩ := hP n hn σ₀
    refine ⟨c * r, σ, mul_ne_zero hc hr, hPσ, fun f z i j hi hj => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun t => congrArg j (Subsingleton.elim _ _)⟩
    have e₁ := H Z f z i j hi (mem_wchart.1 hj 0)
    have e₂ : powVal σ (f ≫ pullback.fst G.hom (jK R)) z i = cst ((f ≫ pullback.fst G.hom (jK R)) ≫ G.hom) z c *
        powVal σ₀ (f ≫ pullback.fst G.hom (jK R)) z i :=
      secIsMul_gs (p := G.hom) (a := c) hσ _ z _ (mem_wchart.2 fun _ => hi)
    rw [Category.assoc, pullback.condition, ← Category.assoc] at e₂
    rw [e₂, e₁, H1.cst_mul, _root_.mul_assoc]
    rfl
  have := A.isAb.proper
  have : CompactSpace A.A.left := QuasiCompact.compactSpace_of_compactSpace A.A.hom
  have : QuasiSeparatedSpace A.A.left := quasiSeparatedSpace_of_quasiSeparated A.A.hom
  have hc := fun N hN => (polAV_nonzeroLocus_cover_affine hL.ample A (N := N) hN).1
  have h₁ : Corresp (L := A.L) (L' := A.L) (fun _ _ => Equiv.refl _) (f₁ ≫ U.gen.hom.left) (f₂ ≫ U.gen.hom.left) := by
    refine corresp_refl hc fun n hn a b z j j' hj hj' => ?_
    obtain ⟨i₁, i₂, m₁, m₂, H⟩ := h z
    obtain ⟨r, σ, hr, hσ, Hσ⟩ := key n hn a
    obtain ⟨s, τ, hs, hτ, Hτ⟩ := key n hn b
    have e : powVal σ (f₁ ≫ pullback.fst G.hom (jK R)) z i₁ * powVal τ (f₂ ≫ pullback.fst G.hom (jK R)) z i₂ =
        powVal τ (f₁ ≫ pullback.fst G.hom (jK R)) z i₁ * powVal σ (f₂ ≫ pullback.fst G.hom (jK R)) z i₂ :=
      H n hn σ τ hσ hτ
    rw [Hσ f₁ z i₁ j m₁ hj, Hσ f₂ z i₂ j' m₂ hj', Hτ f₁ z i₁ j m₁ hj, Hτ f₂ z i₂ j' m₂ hj', hK] at e
    refine ((((ExpInt.isUnit_cst (f₂ ≫ pullback.snd G.hom (jK R)) z hr).mul
      (ExpInt.isUnit_cst (f₂ ≫ pullback.snd G.hom (jK R)) z hs)).mul
      (isoVal w f₁ z i₁ (j 0) ^ (n : ℤ)).isUnit).mul (isoVal w f₂ z i₂ (j' 0) ^ (n : ℤ)).isUnit).mul_left_cancel ?_
    linear_combination e
  have h₂ : Corresp (L := A.L) (L' := A.L) (fun _ _ => Equiv.refl _) (f₂ ≫ U.gen.hom.left) (f₂ ≫ U.gen.hom.left) :=
    corresp_refl hc fun n hn a b z j j' hj hj' => by
      refine (congrArg₂ (· * ·) (sec_trans a _ z hj hj') rfl).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) (sec_trans b _ z hj hj') rfl).symm)
      exact (mul_right_comm _ _ _)
  have e := h₁.unique A.isLB h₂ (n := 4) (by norm_num) id
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (hc 4 le_rfl x))
    (polAV_nonzeroLocus_cover_affine hL.ample A le_rfl).2
  have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
  exact (cancel_mono _).1 e

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralGaugeValuesAreValuationUnits
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.UnitVal

section Values
variable {C : Type} [Field C] {X Y : Scheme.{0}}

theorem valF_appLE' {F : Type} [Field F] {x : Sp F ⟶ X} {U : X.Opens} (f : X ⟶ Y) (W : Y.Opens) (e : U ≤ f ⁻¹ᵁ W)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Y, W)) : valF x U ((f.appLE W U e).hom a) = valF (x ≫ f) W a := by
  have h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ W := fun q hq => e (h hq)
  rw [valF, valF, dite_eq_left h, dite_eq_left h', ← Scheme.Hom.appLE_comp_appLE x f W U ⊤ e h]
  rfl

theorem valF_res' {F : Type} [Field F] {x : Sp F ⟶ X} {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) : valF x V ((X.presheaf.map (homOfLE e).op).hom a) = valF x U a := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => e (h hq)
  rw [valF, valF, dite_eq_left h, dite_eq_left h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]
  rfl

theorem exists_valHom (S : ValuationSubring C) (t : Sp S ⟶ X) (U : X.Opens) (ht : ⊤ ≤ t ⁻¹ᵁ U) :
    ∃ g : Γ(X, U) →+* S, ∀ a, valF (spMap S.subtype ≫ t) U a = g a := by
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.comp (t.appLE U ⊤ ht).hom, fun a => ?_⟩
  have h' : ⊤ ≤ (spMap S.subtype ≫ t) ⁻¹ᵁ U := fun q _ => ht (Set.mem_univ (spMap S.subtype q))
  rw [valF, dite_eq_left h']
  have e : (spMap S.subtype ≫ t).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom =
      t.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom ≫ CommRingCat.ofHom S.subtype := by
    rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap S.subtype) t U ⊤ ⊤ ht le_rfl,
      Category.assoc]
    rfl
  exact congrArg (fun g => g.hom a) e

theorem val_valF_le {S : ValuationSubring C} (t : Sp S ⟶ X) (U : X.Opens)
    (ht : ⊤ ≤ t ⁻¹ᵁ U) (a : Γ(X, U)) : valF (spMap S.subtype ≫ t) U a ∈ S := by
  obtain ⟨g, hg⟩ := exists_valHom S t U ht
  rw [hg]
  exact (g a).2

theorem val_valF_unit {S : ValuationSubring C} (t : Sp S ⟶ X) (U : X.Opens)
    (ht : ⊤ ≤ t ⁻¹ᵁ U) (a : Γ(X, U)) (ha : IsUnit a) : S.valuation (valF (spMap S.subtype ≫ t) U a) = 1 := by
  obtain ⟨g, hg⟩ := exists_valHom S t U ht
  rw [hg]
  exact (S.valuation_eq_one_iff (g a)).1 (ha.map g)
end Values

section Geo
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [Field C] [Algebra (FractionRing R) C]
  {N : NumD C} {ν : NumOf D C N} {S : ValuationSubring C} {s : Sp S ⟶ Sp R}

theorem exists_base (h : ∀ r : R, algebraMap (FractionRing R) C (algebraMap R _ r) ∈ S) :
    ∃ s : Sp S ⟶ Sp R, spMap S.subtype ≫ s = (TF (R := R) C).hom := by
  refine ⟨spMap (((algebraMap (FractionRing R) C).comp (algebraMap R _)).codRestrict S.toSubring h), ?_⟩
  change _ = jFK (R := R) C ≫ jK R
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem base_ext {a b : Sp S ⟶ Sp R} (h : spMap S.subtype ≫ a = spMap S.subtype ≫ b) : a = b := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have := Spec.map_injective h
  congr 1
  ext r
  exact congrArg (fun g => g.hom r) this

theorem isDominant_sub : IsDominant (spMap S.subtype) :=
  ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical S.subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 S.subtype_injective]; exact bot_le)⟩

theorem chart_int (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) (y : Sp S ⟶ D.P.A.left)
    (hy : y ≫ D.P.A.hom = s) : ⊤ ≤ y ⁻¹ᵁ D.P.L.U (ν.J (spMap S.subtype ≫ y)) := by
  obtain ⟨x₀, e, h⟩ := hν (Over.homMk (spMap S.subtype ≫ y) (by rw [Category.assoc, hy, hs]))
  have := D.P.isAb.proper
  have := isDominant_sub (S := S)
  have e' : spMap S.subtype ≫ x₀ = spMap S.subtype ≫ y := e
  obtain rfl : x₀ = y := ext_of_isDominant_of_isSeparated D.P.A.hom
    (base_ext (by rw [← Category.assoc, e', Category.assoc])) _ e'
  exact h

theorem wchart_int (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) {Y : Scheme.{0}} {K : Type}
    [Fintype K] (φ : K → (Y ⟶ D.P.A.left)) (r : Sp S ⟶ Y) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = s) :
    ⊤ ≤ r ⁻¹ᵁ LB.wchart D.P.L φ fun k => ν.J ((spMap S.subtype ≫ r) ≫ φ k) := fun q hq =>
  Set.mem_iInter.2 fun k => by
    beta_reduce
    rw [Category.assoc]
    exact chart_int hν hs (r ≫ φ k) (by rw [Category.assoc, h]) hq

theorem val_vF (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb D.P.L φ ε))
    (r : Sp S ⟶ Y) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = s) {r' : Sp C ⟶ Y} (e : spMap S.subtype ≫ r = r') :
    S.valuation (vF t r' ν.J) = 1 := by
  subst e
  exact val_valF_unit r _ (wchart_int hν hs φ r h) _ (Units.isUnit _)

theorem val_sF (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ} (t : LB.Sec (LB.LinComb D.P.L φ ε))
    (r : Sp S ⟶ Y) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = s) {r' : Sp C ⟶ Y} (e : spMap S.subtype ≫ r = r') :
    sF t r' ν.J ∈ S := by
  subst e
  exact val_valF_le r _ (wchart_int hν hs φ r h) _

theorem exists_ext (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) (x : TF (R := R) C ⟶ D.P.A) :
    ∃ x₀ : Over.mk s ⟶ D.P.A, (Over.homMk (spMap S.subtype) hs : TF (R := R) C ⟶ Over.mk s) ≫ x₀ = x := by
  obtain ⟨x₀, e, -⟩ := hν x
  refine ⟨Over.homMk x₀ (base_ext ?_), Over.OverMorphism.ext e⟩
  rw [← Category.assoc, e, Over.w x]
  exact hs.symm

theorem val_rig (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) :
    S.valuation (vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) C).hom ν.J) = 1 :=
  val_vF hν hs _ s (fun _ => by
    have : eSec D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w η[D.P.A]
    exact (congrArg (s ≫ ·) this).trans (Category.comp_id _)) hs

theorem val_θ (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (x y u : N.A) : S.valuation ((N.θ x y u : C)) = 1 := by
  obtain ⟨x₀, hx⟩ := exists_ext hν hs (ν.eA x)
  obtain ⟨y₀, hy⟩ := exists_ext hν hs (ν.eA y)
  obtain ⟨u₀, hu⟩ := exists_ext hν hs (ν.eA u)
  rw [ν.θ_eq]
  refine val_vF hν hs _ (lift x₀ (lift y₀ u₀)).left (fun k => ?_) ?_
  · exact (congrArg (_ ≫ ·) (Over.w (psum D.P.A (x3 D.P.A) k.down))).trans (Over.w (lift x₀ (lift y₀ u₀)))
  · rw [← hx, ← hy, ← hu, ← comp_lift, ← comp_lift]
    rfl

theorem val_σ (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (x : N.A) : S.valuation ((N.σ x : C)) = 1 := by
  obtain ⟨x₀, hx⟩ := exists_ext hν hs (ν.eA x)
  rw [ν.σ_eq]
  refine val_vF hν hs _ x₀.left (fun k => ?_) (congrArg (·.left) hx)
  fin_cases k
  · exact (congrArg (_ ≫ ·) (Over.w ι[D.P.A])).trans (Over.w x₀)
  · exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Over.w x₀)

theorem val_th (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (x : N.A) : N.th x ∈ S := by
  obtain ⟨x₀, hx⟩ := exists_ext hν hs (ν.eA x)
  have h := congrArg S.valuation (ν.th_eq x)
  rw [map_mul, val_rig hν hs, _root_.mul_one] at h
  rw [← S.valuation_le_one_iff, h, S.valuation_le_one_iff]
  exact val_sF hν hs _ x₀.left (fun _ => (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Over.w x₀))
    (congrArg (·.left) hx)

theorem val_psi (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (χ : D.X) (hχ : PsiUnitOn D χ Set.univ) : S.valuation (vF (D.psi χ) (jFK (R := R) C) ν.J) = 1 := by
  have e : jFK (R := R) C ≫ D.xK χ = spMap S.subtype ≫ s ≫ (D.c χ).left := by
    rw [← Category.assoc, hs]
    exact (Category.assoc _ _ _).symm
  have h1 := chart_int hν hs (s ≫ (D.c χ).left)
    ((Category.assoc _ _ _).trans ((congrArg (s ≫ ·) (Over.w (D.c χ))).trans (Category.comp_id _)))
  rw [← e] at h1
  have h2 : s (IsLocalRing.closedPoint S) ∈ ((D.c χ).left ⁻¹ᵁ D.P.L.U (ν.J (jFK (R := R) C ≫ D.xK χ)) : (Sp R).Opens) :=
    h1 (Set.mem_univ _)
  obtain ⟨_, ⟨V, hV, rfl⟩, hy, hle⟩ := (Sp R).isBasis_affineOpens.exists_subset_of_mem_open h2 (TopologicalSpace.Opens.isOpen _)
  have h3 : ⊤ ≤ s ⁻¹ᵁ V := ((IsLocalRing.closedPoint_mem_iff (s ⁻¹ᵁ V)).1 hy).ge
  have h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U
      (fun _ => ν.J (jFK (R := R) C ≫ D.xK χ)) := fun y hy => Set.mem_iInter.2 fun _ => hle hy
  obtain ⟨r, hr, er⟩ := hχ (fun _ => ν.J (jFK (R := R) C ≫ D.xK χ)) V hV (Set.subset_univ _) hle h
  have hs' : jFK (R := R) C ≫ jK R = spMap S.subtype ≫ s := hs.symm
  have h4 : ⊤ ≤ jFK (R := R) C ⁻¹ᵁ (jK R ⁻¹ᵁ V) := by
    change ⊤ ≤ (jFK (R := R) C ≫ jK R) ⁻¹ᵁ V
    rw [hs']
    exact fun q _ => h3 (Set.mem_univ (spMap S.subtype q))
  have a := valF_res' h h4 ((D.psi χ).s _).val
  rw [Scheme.Hom.app_eq_appLE] at er
  refine (congrArg S.valuation (a.symm.trans ((congrArg (valF _ _) er.symm).trans
    (valF_appLE' (jK R) V le_rfl h4 r)))).trans ?_
  exact (congrArg (fun q => S.valuation (valF q V r)) hs').trans (val_valF_unit s V h3 r hr)

theorem val_ψ (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (χ : N.X) (hχ : PsiUnitOn D (ν.eX χ) Set.univ) : S.valuation ((N.ψ χ : C)) = 1 := by
  rw [ν.ψ_eq, map_mul, val_rig hν hs, val_psi hν hs _ hχ, _root_.mul_one]
end Geo

theorem integral_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (S : ValuationSubring F), (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) → ∀ (N : NumD F) (ν : NumOf D F N), ν.Integral S → (∀ x y u, S.valuation (N.θ x y u : F) = 1) ∧ (∀ x, S.valuation (N.σ x : F) = 1) ∧ (∀ x, N.th x ∈ S) ∧ ((∀ y, PsiUnitOn D y Set.univ) → ∀ χ, S.valuation (N.ψ χ : F) = 1) := by
  intro R _ _ D F _ _ S hR N ν hν
  obtain ⟨s, hs⟩ := exists_base (R := R) (S := S) hR
  exact ⟨val_θ hν hs, val_σ hν hs, val_th hν hs, fun h χ => val_ψ hν hs χ (h _)⟩

end GlobalTheory.Ex.UnitVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsThetaPtDown
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ThetaNest
open ThetaCoord CommPairing GlobalLift

variable {S : Scheme.{0}} {T : Over S}

theorem isThetaPt_of_over (P : PolAV S) [Subsingleton T.left] {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)}
    {v : I → Γ(T.left, ⊤)} (ho : Odd k) (hu : IsUnit (k : Γ(T.left, ⊤))) (H : IsThetaPtOver P k x v) :
    IsThetaPt P k x v := by
  refine ⟨ho, hu, fun p => ⟨⊤, trivial, ?_⟩⟩
  obtain ⟨h, hh⟩ := exists_section (T := T) (V := ⊤) (p := p) trivial
  have hi : overResι (T := T) ⊤ ≫ h = 𝟙 _ := by
    haveI : Mono (overResι (T := T) ⊤) := Over.mono_of_mono_left _ (hk := inferInstanceAs (Mono (⊤ : T.left.Opens).ι))
    rw [← cancel_mono (overResι (T := T) ⊤), Category.assoc, hh, Category.comp_id, Category.id_comp]
  exact isThetaPtOver_pull P H _ h hi

theorem weilIs_one_left (hG : GlobalFnsSt) (P : PolAV S) {k : ℤ} {ν : LB.Gen (negLB P.A P.L k T)} (hν : ν.IsGen)
    (θ : ThetaGrp P.A P.L k T) : WeilIs P.A P.L k 1 θ.pt 1 := by
  obtain ⟨o, ho, hv⟩ := exists_symLift_one P.isLB hν 1
  rw [← ho.pt_eq]
  refine weilIs_of_commIsOf hG P.isAb P.isLB ((commIsOf_iff P.isLB _ _ _).2 fun Z r z J hJ => ?_)
  have e : translT P.A (1 : T ⟶ P.A) = 𝟙 _ := by
    rw [translT, ThetaAct.translPt_one, lift_fst_snd]
  rw [hv _ _ z J hJ, hv _ _ z J hJ, ho.pt_eq, e, map_one]
  simp

theorem isThetaPtOver_down (hG : GlobalFnsSt) (P : PolAV S) [Subsingleton T.left] {n m : ℕ} (ho : Odd (n * m))
    {I : Type} {x : I → (T ⟶ P.A)} {v v' : I → Γ(T.left, ⊤)} (hx : ∀ i, (x i ^ n) ^ m ^ 2 = 1)
    (H : IsThetaPtOver P (n * m) x v) (H' : IsThetaPtOver P m (fun i => x i ^ n) v') :
    IsThetaPtOver P m (fun i => x i ^ n) v := by
  rcases isEmpty_or_nonempty I with hI | ⟨⟨i₀⟩⟩
  · rwa [Subsingleton.elim v v']
  obtain ⟨th', s', α', τ', W, t', w', u', hth', hα', hτ', hs', hW, ht', hw', hv⟩ := H
  obtain ⟨th, s, α, τ, U, t, -, -, hth, hα, hτ, hs, hU, ht, -, -⟩ := H'
  obtain ⟨ρ, hρ⟩ := exists_unit_of_isGenSec hth hth'
  obtain ⟨ν, hν, -⟩ := (hW i₀).sym
  obtain ⟨o, hoo, -⟩ := exists_symLift_one P.isLB hν ((n * m) ^ 2)
  obtain ⟨u, hu⟩ := exists_unit_isValueAt hG P.isAb P.isLB (r := n) (q := m ^ 2) rfl
    (pow_dvd_pow_of_dvd (Dvd.intro_left n rfl) 2) ho.pow hρ hα hα' hs hs' hτ' (one_pow n) hoo hτ
  refine ⟨th, s, α, τ, U, t, fun i => ρ * u * w' i, u' * (ρ * u)⁻¹, hth, hα, hτ, hs, hU, ht, fun i => ?_, fun i => ?_⟩
  · have := hu (x i) (U i) (t i) (W i) (t' i) (w' i) 1
      (by rw [show (n * m) ^ 2 = n * m ^ 2 * n by ring, pow_mul, pow_mul, hx, one_pow]) (hU i) (ht i)
      (by rw [_root_.mul_one]; exact hW i) (ht' i) (hw' i)
      (by rw [← (hW i).pt_eq]; exact weilIs_one_left hG P hν _)
    rwa [one_pow, Units.val_one, _root_.mul_one] at this
  · rw [hv, ← Units.val_mul, ← _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel_right]

theorem isThetaPt_down : Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (n m : ℕ) (Ix : Type)
    (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → Γ((baseOver (Sp K)).left, ⊤)),
    (∀ i, (x i ^ n) ^ m ^ 2 = 1) → IsThetaPt P (n * m) x v → IsThetaPt P m (fun i => x i ^ n) v := by
  intro hL K _ _ P n m Ix x v hx H
  haveI : Subsingleton (baseOver (Sp K)).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  haveI : Nonempty (baseOver (Sp K)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have ho : Odd m := (Nat.odd_mul.1 H.1).2
  have hu : IsUnit (m : Γ((baseOver (Sp K)).left, ⊤)) :=
    isUnit_of_mul_isUnit_right (by rw [← Nat.cast_mul]; exact H.2.1)
  have hK : (m : K) ≠ 0 := by
    have := IsUnit.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom hu
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨v', H'⟩ := ThetaPtExist.exists_isThetaPt hL K P m ho hK (fun i => x i ^ n) hx
  exact isThetaPt_of_over P ho hu (isThetaPtOver_down hL.globalFns P H.1 hx (isThetaPtOver_of_subsingleton P H)
    (isThetaPtOver_of_subsingleton P H'))

end GlobalTheory.ThetaNest
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QvalAddTower
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.NestQVal

attribute [local instance] GlobalTheory.TorusExt.gtGroup


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in
theorem _root_.GlobalTheory.NestQVal.qval_add_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H), ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIsoQ D D₀ oa F) (N : _root_.GlobalTheory.Ex.NumD F) (ν : _root_.GlobalTheory.Ex.NumOf D₀ F N) (q : ∀ n : ℕ, D.La → N.QT n), (∀ g, ∃! c, ν.Pt g c) → (∀ g g' g'' c c' c'', ν.Pt g c → ν.Pt g' c' → ν.Pt g'' c'' → (_root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF.IsAdd g g' g'' ↔ c'' = c * c')) → (∀ k, (∀ p : _root_.ReciprocityTheory.ChartRestriction.G.Out.QkPt D₀ F k, ∃! q, ν.QPt p q) ∧ ∀ (p p' : _root_.ReciprocityTheory.ChartRestriction.G.Out.QkPt D₀ F k) q q', ν.QPt p q → ν.QPt p' q' → (_root_.ReciprocityTheory.ChartRestriction.G.Out.QkPt.Equiv D₀ F p p' ↔ N.QEq q q')) → (∀ n a, ν.QPt (I.ev n a) (q n a)) → (∀ n, 0 < n → ∀ a b, N.QEq (q n a * q n b) (q n (a + b))) ∧ ∀ n m, 0 < n → 0 < m → ∀ a (p : N.QT n), p.1.1 = (q (n * m) a).1.1 → p.1.2 = (q (n * m) a).1.2 ^ m → N.QEq p (q n a) := by
  intro E _ _ _ H D R _ _ D₀ _ oa _ _ F _ _ _ I N ν q hPt hAdd hQ hev

  have hzero : ν.Pt 0 1 := by
    obtain ⟨c, hc, -⟩ := hPt 0
    have h := (hAdd 0 0 0 c c c hc hc hc).1 ((_root_.GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (add_zero 0).symm)
    have : c = 1 := by simpa using (mul_eq_left.1 h.symm)
    simpa [this] using hc
  have hsmul : ∀ (m : ℕ) g c, ν.Pt g c → ν.Pt (m • g) (c ^ m) := by
    intro m g c hc
    induction m with
    | zero => simpa using hzero
    | succ k ih =>
      obtain ⟨c', hc', -⟩ := hPt ((k + 1) • g)
      have h := (hAdd _ _ _ _ _ _ ih hc hc').1 ((_root_.GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (succ_nsmul g k))
      simpa [h, pow_succ] using hc'
  refine ⟨fun n hn a b => ?_, fun n m hn hm a p hp1 hp2 => ?_⟩
  · obtain ⟨r, hry, hrg, hr⟩ := I.add n hn a b
    obtain ⟨hya, hga⟩ := hev n a
    obtain ⟨hyb, hgb⟩ := hev n b
    obtain ⟨c'', hc'', -⟩ := hPt r.g
    have hc := (hAdd _ _ _ _ _ _ hga hgb hc'').1 hrg
    have hrs : ν.QPt r (q n a * q n b) := by
      refine ⟨?_, ?_⟩
      · simp [hry, ← hya, ← hyb]
      · simpa [hc] using hc''
    exact ((hQ n).2 _ _ _ _ hrs (hev n (a + b))).1 hr
  · obtain ⟨Q, hQy, hQg, hQe⟩ := I.tower n m hn hm a
    obtain ⟨hy, hg⟩ := hev (n * m) a
    have hQp : ν.QPt Q p := by
      refine ⟨?_, ?_⟩
      · rw [hQy, ← hy, hp1]
      · rw [(_root_.GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hQg, hp2]
        exact hsmul m _ _ hg
    exact ((hQ n).2 _ _ _ _ hQp (hev n a)).1 hQe

end GlobalTheory.NestQVal
end

