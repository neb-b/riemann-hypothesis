module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefRiemannRochAsymptotic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmSpMapUnitOn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.PsiMono
variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

def fracPt (ρ : V →+* V₁) (hρ : Function.Injective ρ) : (TK V₁).left ⟶ (TK V).left :=
  spMap (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ)

theorem fracPt_comp (ρ : V →+* V₁) (hρ : Function.Injective ρ) : fracPt ρ hρ ≫ jK V = jK V₁ ≫ spMap ρ := by
  simp only [fracPt, spMap, jK, TK, Over.mk_hom, ← Spec.map_comp]
  congr 1
  ext x
  simp [IsFractionRing.map, IsLocalization.map_eq]

theorem gm_spMap_unitOn {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (z : Sp R') (k : Rˣ) :
    gm (spMap f) z ⊤ (unitOn k) = gm (𝟙 _) z ⊤ (unitOn (Units.map f.toMonoidHom k)) := by
  have h := gm_pull (𝟙 _) (spMap f) z ⊤ trivial (unitOn k)
  rw [Category.id_comp] at h
  refine h.symm.trans (congrArg _ ?_)
  ext
  have e := congrArg (fun g => g.hom (k : R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [unitOn, pullU, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  exact e.symm

theorem val_scaleGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (c : Γ(Y, ⊤)ˣ) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (scaleGen t c) r z J = gm r z ⊤ c * val t r z J :=
  gm_scaleGen t c r z _ (hJ.mem φ r)

theorem prod_zpow_swap {F : Type} [Field F] {I C : Type} [Fintype I] [Fintype C] (x : I → F) (e : C → I → ℤ)
    (w : C → ℤ) (h : ∀ c, ∏ i, x i ^ e c i ≠ 0) :
    ∏ c, (∏ i, x i ^ e c i) ^ w c = ∏ i, x i ^ ∑ c, w c * e c i := by
  classical
  have hz : ∀ i, x i = 0 → ∀ c, e c i = 0 := by
    intro i hi c
    by_contra hne
    exact h c (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, zero_zpow _ hne]))
  set y : I → F := fun i => if x i = 0 then 1 else x i with hy
  have hy0 : ∀ i, y i ≠ 0 := fun i => by
    by_cases hi : x i = 0 <;> simp [hy, hi]
  have hxy : ∀ i (n : ℤ), (x i = 0 → n = 0) → x i ^ n = y i ^ n := by
    intro i n hn
    by_cases hi : x i = 0
    · rw [hn hi]; simp
    · simp [hy, hi]
  have l1 : ∀ c, ∏ i, x i ^ e c i = ∏ i, y i ^ e c i :=
    fun c => Finset.prod_congr rfl fun i _ => hxy i _ fun hi => hz i hi c
  have l2 : ∀ i, x i ^ ∑ c, w c * e c i = y i ^ ∑ c, w c * e c i := fun i => hxy i _ fun hi => by
    simp [hz i hi]
  simp_rw [l1, l2, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  have key : ∀ (a : F), a ≠ 0 → ∀ (s : Finset C) (n : C → ℤ), ∏ c ∈ s, a ^ n c = a ^ ∑ c ∈ s, n c := by
    intro a ha s n
    induction s using Finset.induction_on with
    | empty => simp
    | insert c s hc ih => rw [Finset.prod_insert hc, Finset.sum_insert hc, ih, zpow_add₀ ha]
  rw [key _ (hy0 i)]
  exact congrArg _ (Finset.sum_congr rfl fun c _ => mul_comm _ _)

abbrev fracOver (ρ : V →+* V₁) (hρ : Function.Injective ρ) : Over (Sp V) := Over.mk (fracPt ρ hρ ≫ jK V)

theorem psi_val (W : Matrix (Fin 8) (Fin 8) ℤ) (Q : Data V) (ρ : V →+* V₁) (hρ : Function.Injective ρ) (D : DegPre V₁)
    (e : (Fin 8 → Q.X) ≃+ D.X) (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2))))
    (hw : ∀ κ : (TK V₁).left ⟶ (TK V).left, κ ≫ jK V = jK V₁ ≫ spMap ρ → ∀ mu z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.psi (e mu)) (𝟙 _) z J' =
        gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
            pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
          ∏ a, ∏ b, val (Q.tau (mu a) (mu b)) κ z J ^ W a b)
    (τ₀ : Gens Q) {n : ℕ} (s : Fin n → V) (ε : Fin n → LinearMap.BilinForm ℤ Q.X) (hτ : TauIn Q τ₀ s ε)
    {W₀ : Type} [CommRing W₀] (ib : W₀ →+* V) (B₀ : Over (Sp W₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left)
    (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀)) (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (lamPts (c₀ a) (c₀ b)) negε))
    (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left) (w₀ : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂))
    (h₀ : ∀ (T : Over (Sp V)) (a b : Q.X) z J J', Good M₀ z J → Good Q.M.L z J' →
      val (τ₀ a b) (toUnit T).left z J' =
        lamVal w₀ (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left z J J' * val (τ₁ a b) (T.hom ≫ spMap ib) z J)
    (mu : Fin 8 → Q.X) (z : (TK V₁).left) (J : ((TK V₁).left ⟶ Q.B.left) → Q.M.L.ι)
    (J' : ((TK V₁).left ⟶ D.P.A.left) → D.P.L.ι) (J₀ : ((TK V₁).left ⟶ B₀.left) → M₀.ι)
    (hJ : Good Q.M.L z J) (hJ' : Good D.P.L z J') (hJ₀ : Good M₀ z J₀) :
    ∃ u : (FractionRing V₁)ˣ, (u : FractionRing V₁) = ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ qW W (ε i) mu ∧
      val (D.psi (e mu)) (𝟙 _) z J' =
        gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
            pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
          (∏ a, ∏ b, (lamVal (Z := (TK V₁).left) w₀ (lift (toUnit (fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (fracOver ρ hρ) ≫ Q.c (mu b))).left
              z J₀ J * val (τ₁ (mu a) (mu b)) ((fracPt ρ hρ ≫ jK V) ≫ spMap ib) z J₀) ^ W a b) *
          gm (𝟙 _) z ⊤ (unitOn u) := by
  classical
  have hL : Q.M.L.IsLB := Q.M.isLB
  choose k hk hkv using fun a b => (hτ a b).2
  have htau : ∀ a b, val (Q.tau a b) (fracPt ρ hρ) z J =
      gm (fracPt ρ hρ) z ⊤ (unitOn (k a b)) * val (τ₀ a b) (fracPt ρ hρ ≫ jK V) z J := by
    intro a b
    let t₁ := scaleGen (LB.pullGen Q.M.L (lamPts (Q.c a) (Q.c b)) negε (τ₀ a b) (toUnit (TK V)).left) (unitOn (k a b))
    have hc : LB.Gen.Corr Q.M.L _ _ _ _ (Q.tau a b) t₁ := corr_of_val hL fun y J₁ hJ₁ => by
      rw [val_scaleGen _ _ _ _ hJ₁, val_pull hJ₁, Category.id_comp]
      exact hkv a b y J₁ hJ₁
    rw [val_corr hJ hc (fracPt ρ hρ), val_scaleGen _ _ _ _ hJ, val_pull hJ]
    rfl
  have hunit : ∀ a b, gm (fracPt ρ hρ) z ⊤ (unitOn (k a b)) =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ).toMonoidHom
        (k a b))) := fun a b => gm_spMap_unitOn _ z _
  have hbase : ∀ a b, val (τ₀ a b) (fracPt ρ hρ ≫ jK V) z J =
      lamVal (Z := (TK V₁).left) w₀ (lift (toUnit (fracOver ρ hρ) ≫ Q.c a) (toUnit (fracOver ρ hρ) ≫ Q.c b)).left z J₀ J *
        val (τ₁ a b) ((fracPt ρ hρ ≫ jK V) ≫ spMap ib) z J₀ := fun a b => h₀ (fracOver ρ hρ) a b z J₀ J hJ₀ hJ
  have hfk : ∀ a b, ((Units.map (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ).toMonoidHom
      (k a b) : (FractionRing V₁)ˣ) : FractionRing V₁) =
        ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ ε i a b := by
    intro a b
    show IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ (k a b : FractionRing V) = _
    rw [hk a b, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow₀]
    simp [IsFractionRing.map, IsLocalization.map_eq]
  refine ⟨∏ a, ∏ b, Units.map (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ).toMonoidHom
      (k (mu a) (mu b)) ^ W a b, ?_, ?_⟩
  · simp_rw [Units.coe_prod, Units.val_zpow_eq_zpow_val, hfk]
    have hne : ∀ c : Fin 8 × Fin 8, ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ ε i (mu c.1) (mu c.2) ≠ 0 :=
      fun c => by rw [← hfk]; exact Units.ne_zero _
    have e := prod_zpow_swap (fun i => algebraMap V₁ (FractionRing V₁) (ρ (s i)))
      (fun (c : Fin 8 × Fin 8) i => ε i (mu c.1) (mu c.2)) (fun (c : Fin 8 × Fin 8) => W c.1 c.2) hne
    rw [Fintype.prod_prod_type] at e
    simp only [Fintype.sum_prod_type] at e
    rw [e]
    rfl
  · rw [hw (fracPt ρ hρ) (fracPt_comp ρ hρ) mu z J J' hJ hJ', _root_.mul_assoc]
    congr 1
    clear hw h₀ hkv hk hτ hfk
    simp only [htau, hunit, hbase]
    simp only [unitOn, map_prod, map_zpow, mul_zpow, Finset.prod_mul_distrib]
    exact _root_.mul_comm _ _

theorem psi_val_of (W : Matrix (Fin 8) (Fin 8) ℤ) (Q : Data V) (ρ : V →+* V₁) (hρ : Function.Injective ρ) (D : DegPre V₁)
    (e : (Fin 8 → Q.X) ≃+ D.X) (hS : SharpRef W Q ρ D e) (τ₀ : Gens Q) {n : ℕ} (s : Fin n → V)
    (ε : Fin n → LinearMap.BilinForm ℤ Q.X) (hτ : TauIn Q τ₀ s ε) {W₀ : Type} [CommRing W₀] (ib : W₀ →+* V)
    (hB : FromBase Q τ₀ ib) :
    ∃ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
      (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
        (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))),
      (∀ a, IsMonHom (pr a)) ∧
      (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) ∧
      w.IsGen ∧ (∀ mu a, (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = spMap ρ ≫ (Q.c (mu a)).left) ∧
      ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀))
        (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (lamPts (c₀ a) (c₀ b)) negε))
        (β : Q.B.left ⟶ B₀.left) (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left)
        (w₀ : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂)),
        IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.B B₀ (spMap ib) β ∧ IsSquare β β₂ ∧ w₀.IsGen ∧
        (∀ a, (Q.c a).left ≫ β = spMap ib ≫ (c₀ a).left) ∧ (∀ a b, (τ₁ a b).IsGen) ∧
        (∀ (T : Over (Sp V)) (a b : Q.X) z J J', Good M₀ z J → Good Q.M.L z J' →
          val (τ₀ a b) (toUnit T).left z J' =
            lamVal w₀ (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left z J J' * val (τ₁ a b) (T.hom ≫ spMap ib) z J) ∧
        ∀ (mu : Fin 8 → Q.X) (z : (TK V₁).left) (J : ((TK V₁).left ⟶ Q.B.left) → Q.M.L.ι)
          (J' : ((TK V₁).left ⟶ D.P.A.left) → D.P.L.ι) (J₀ : ((TK V₁).left ⟶ B₀.left) → M₀.ι),
          Good Q.M.L z J → Good D.P.L z J' → Good M₀ z J₀ →
          ∃ u : (FractionRing V₁)ˣ,
            (u : FractionRing V₁) = ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ qW W (ε i) mu ∧
            val (D.psi (e mu)) (𝟙 _) z J' =
              gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
                  pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
                (∏ a, ∏ b, (lamVal (Z := (TK V₁).left) w₀
                    (lift (toUnit (fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (fracOver ρ hρ) ≫ Q.c (mu b))).left
                    z J₀ J * val (τ₁ (mu a) (mu b)) ((fracPt ρ hρ ≫ jK V) ≫ spMap ib) z J₀) ^ W a b) *
                gm (𝟙 _) z ⊤ (unitOn u) := by
  obtain ⟨pr, w, h1, h2, h3, h4, hw⟩ := hS
  obtain ⟨B₀, _, _, M₀, c₀, τ₁, β, β₂, w₀, g1, g2, g3, g4, g5, g6, g7, h₀⟩ := hB
  exact ⟨pr, w, h1, h2, h3, h4, B₀, inferInstance, inferInstance, M₀, c₀, τ₁, β, β₂, w₀, g1, g2, g3, g4, g5, g6, g7, h₀,
    fun mu z J J' J₀ hJ hJ' hJ₀ => psi_val W Q ρ hρ D e pr w hw τ₀ s ε hτ ib B₀ M₀ c₀ τ₁ β₂ w₀ h₀ mu z J J' J₀ hJ hJ' hJ₀⟩

end GlobalTheory.Poinc.PsiMono

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolRoot

def Root {S T : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (G2 A).left) (t : T ⟶ S) : Prop :=
  ∃ (B : Over T) (_ : GrpObj B) (_ : IsCommMonObj B) (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left),
    IsGrpPullback B A t β ∧ IsSquare β β₂ ∧ ∃ L : LB B.left, L.IsLB ∧ LBIso (abelian₂ B L) (P.pull β₂)

theorem Root.comp {S T T' : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {P : LB (G2 A).left}
    {t : T ⟶ S} (h : Root A P t) (σ : T' ⟶ T) : Root A P (σ ≫ t) := by
  obtain ⟨A', _, _, β, β₂, hβ, hsq, L, hL, H⟩ := h
  obtain ⟨B', _, φ, hφ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A' σ
  haveI : IsCommMonObj B' := by
    rw [isCommMonObj_iff_isMulCommutative]
    intro T
    refine ⟨⟨fun x y => Over.OverMorphism.ext (hφ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
    rw [← hφ.2 T x y (pushPt hφ.1.w x) (pushPt hφ.1.w y) rfl rfl,
      ← hφ.2 T y x (pushPt hφ.1.w y) (pushPt hφ.1.w x) rfl rfl, _root_.mul_comm]
  let V := lift (pushPt hφ.1.w (fst B' B')) (pushPt hφ.1.w (snd B' B'))
  have hV : IsSquare φ V.left := GlobalTheory.LamPull.exists_isSquare hφ.1.w
  refine ⟨B', inferInstance, inferInstance, φ ≫ β, V.left ≫ β₂, hφ.comp hβ,
    GlobalTheory.ZM.SiegPull.isSquare_comp hV hsq, L.pull φ, pull_isLB hL φ, ?_⟩
  refine LBIso.chartPull
    (chartPullLinComb L φ _ _ _ V.left fun I => psum_push hφ _ _ V (fun i => ?_) I.down)
    (chartPullSame P (fun _ : PUnit => V.left ≫ β₂) (fun _ => β₂) (fun _ => 1) V.left fun _ => rfl) H
  fin_cases i <;> simp [V, x2]

def tri {X Y T : Scheme.{0}} (f : X ⟶ Y) (a b c : T ⟶ X) (h₁ : a ≫ f = b ≫ f) (h₂ : b ≫ f = c ≫ f) :
    T ⟶ GlobalTheory.LBDescent.Triple f :=
  pullback.lift (pullback.lift a b h₁) (pullback.lift b c h₂) (by rw [pullback.lift_snd, pullback.lift_fst])

def TriCocycle {X Y : Scheme.{0}} (f : X ⟶ Y) (D : Γ(GlobalTheory.LBDescent.Triple f, ⊤)ˣ) : Prop :=
  ∀ (T : Scheme.{0}) (a b c d : T ⟶ X) (h₁ : a ≫ f = b ≫ f) (h₂ : b ≫ f = c ≫ f) (h₃ : c ≫ f = d ≫ f),
    GlobalTheory.CharKer.pullTop (tri f a b c h₁ h₂) D * GlobalTheory.CharKer.pullTop (tri f a c d (h₁.trans h₂) h₃) D =
      GlobalTheory.CharKer.pullTop (tri f b c d h₂ h₃) D * GlobalTheory.CharKer.pullTop (tri f a b d h₁ (h₂.trans h₃)) D

def KillsSq {X Y : Scheme.{0}} (f : X ⟶ Y) (D : Γ(GlobalTheory.LBDescent.Triple f, ⊤)ˣ) (u : Γ(pullback f f, ⊤)ˣ) : Prop :=
  D ^ 2 * GlobalTheory.CharKer.pullTop (pullback.fst (pullback.snd f f) (pullback.fst f f)) u *
      GlobalTheory.CharKer.pullTop (pullback.snd (pullback.snd f f) (pullback.fst f f)) u =
    GlobalTheory.CharKer.pullTop (GlobalTheory.LBDescent.pr13 f) u

end GlobalTheory.PolRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H0LowerBoundIntersectionNumberClosure
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClosureRR

theorem eventually_le_of_abs_sub_le (k C : ℕ) (T : ℤ) (q : ℚ) (hq : q < T) (h : ℕ → ℕ)
    (hC : ∀ m : ℕ, |(k.factorial : ℤ) * (h m : ℤ) - T * (m : ℤ) ^ k| ≤
      C * ((k : ℤ) * ((m : ℤ) + 1) ^ (k - 1))) :
    ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → q * (l : ℚ) ^ k / k.factorial ≤ (h l : ℚ) := by
  have hf : (0 : ℚ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hε : (0 : ℚ) < (T : ℚ) - q := sub_pos.2 hq
  obtain ⟨N, hN⟩ := exists_nat_ge ((C : ℚ) * k * 2 ^ (k - 1) / ((T : ℚ) - q))
  refine ⟨N + 1, fun l hl => ?_⟩
  have hm : (1 : ℚ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
  have hNl : (N : ℚ) ≤ l := by exact_mod_cast (show N ≤ l by omega)
  have hB : (C : ℚ) * k * 2 ^ (k - 1) ≤ ((T : ℚ) - q) * l := by
    have := (div_le_iff₀ hε).1 (hN.trans hNl)
    linarith
  have a := hC l
  rw [abs_le] at a
  have a' : (T : ℚ) * (l : ℚ) ^ k - (C : ℚ) * ((k : ℚ) * ((l : ℚ) + 1) ^ (k - 1)) ≤
      (k.factorial : ℚ) * (h l : ℚ) := by
    have := a.1
    have e : ((T * (l : ℤ) ^ k - C * ((k : ℤ) * ((l : ℤ) + 1) ^ (k - 1)) : ℤ) : ℚ) ≤
        (((k.factorial : ℤ) * (h l : ℤ) : ℤ) : ℚ) := Int.cast_le.2 (by linarith)
    push_cast at e
    exact e
  rw [div_le_iff₀ hf]
  rcases k with _ | j
  · simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, CharP.cast_eq_zero, zero_mul,
      mul_zero, sub_zero, one_mul] at a' ⊢
    linarith
  · simp only [Nat.add_sub_cancel] at a' hB
    have h2 : ((l : ℚ) + 1) ^ j ≤ 2 ^ j * (l : ℚ) ^ j := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) j
    have hl0 : (0 : ℚ) ≤ (l : ℚ) ^ j := by positivity
    have hCk : (0 : ℚ) ≤ (C : ℚ) * ((j + 1 : ℕ) : ℚ) := by positivity
    have e1 : (C : ℚ) * (((j + 1 : ℕ) : ℚ) * ((l : ℚ) + 1) ^ j) ≤
        (C : ℚ) * ((j + 1 : ℕ) : ℚ) * 2 ^ j * (l : ℚ) ^ j := by
      have := mul_le_mul_of_nonneg_left h2 hCk
      nlinarith
    have e2 : (C : ℚ) * ((j + 1 : ℕ) : ℚ) * 2 ^ j * (l : ℚ) ^ j ≤ ((T : ℚ) - q) * l * (l : ℚ) ^ j :=
      mul_le_mul_of_nonneg_right hB hl0
    rw [pow_succ] at a' ⊢
    nlinarith

end GlobalTheory.ClosureRR

namespace GlobalTheory.ClosureRR

theorem h0_ge_of_lt_interNumRed : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X) (k : ℕ) (q : ℚ),
  IsAmpleLB (toLB A) → letI := algebraΓOfHom p; topologicalKrullDim (closure ({z} : Set X)) = k →
  q < (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) →
  ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → q * (l : ℚ) ^ k / k.factorial ≤
    (letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p);
      lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) : ℚ) := by
  intro X _ _ p hp A z k q hA
  letI := algebraΓOfHom p
  intro hdim hq
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p)
  have hi : ∀ r : ℂ, (redι (Closeds.closure ({z} : Set X))).appTop (algebraMap ℂ Γ(X, ⊤) r) =
      algebraMap ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤) r :=
    fun r => rfl
  have hpq : IsProjOver (redι (Closeds.closure ({z} : Set X)) ≫ p) := by
    obtain ⟨n, f, hf, hs⟩ := hp
    exact ⟨n, redι (Closeds.closure ({z} : Set X)) ≫ f, inferInstance, by rw [Category.assoc, hs]⟩
  have hstr : strHom ℂ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme =
      redι (Closeds.closure ({z} : Set X)) ≫ p := strHom_eq fun _ => rfl
  have hD : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme = k :=
    (topologicalKrullDim_red _).trans hdim
  have hNef : IsNef ℂ ((toLB A).pull (redι (Closeds.closure ({z} : Set X)))) :=
    (IsAmpleLB.isNef (k := ℂ) hA).pull_of_isClosedImmersion _ hi
  obtain ⟨C, hC⟩ := NefRiemannRoch.abs_factorial_mul_sections_sub_top_le ℂ _ (hstr ▸ hpq) k hD.le _ hNef
  have heq : interNumRed ℂ (Closeds.closure ({z} : Set X)) (fun _ : Fin k => toLB A) =
      topSelfIntersection ℂ ((toLB A).pull (redι (Closeds.closure ({z} : Set X)))) k :=
    interNumOn_const_eq_topSelf hi (isLB_toLB A) k
  have hH : ∀ l : ℕ, lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) =
      lbH0 ℂ (lbPow ((toLB A).pull (redι (Closeds.closure ({z} : Set X)))) l) := fun l =>
    lineBundleGlobalSectionsDim_congr_picardClass (pull_isLB (isLB_toLB _) _) (isLB_lbPow (pull_isLB (isLB_toLB A) _) l)
      (by rw [cls_lbPow (pull_isLB (isLB_toLB A) _), cls_pull (isLB_toLB _), cls_pull (isLB_toLB A),
        ← toPic_apply, ← toPic_apply, map_nsmul, map_nsmul])
  rw [heq] at hq
  obtain ⟨l₁, hl₁⟩ := eventually_le_of_abs_sub_le k C _ q hq _ hC
  exact ⟨l₁, fun l hl => by rw [hH l]; exact hl₁ l hl⟩

end GlobalTheory.ClosureRR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateConditionsIffPullbacks
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.HTTransport

open ReciprocityTheory.ChartRestriction.G.Pdiv

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

def tateTransport {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q'] {act : D.O → Q → Q}
    {act' : D.O → Q' → Q'} {E : ℕ → Q → Q → kˣ → Prop} {E' : ℕ → Q' → Q' → kˣ → Prop}
    (I : TateIsoO D k Q act E) (e : Q ≃* Q') (ha : ∀ c g, e (act c g) = act' c (e g))
    (hE : ∀ n g g' u, E n g g' u → E' n (e g) (e g') u) : TateIsoO D k Q' act' E' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n y := e (I.ev n y)
  add n x y := by rw [I.add, map_mul]
  lin n c x := by rw [I.lin, ha]
  ker n hn hp x := by rw [map_eq_one_iff _ e.injective]; exact I.ker n hn hp x
  onto n hn hp q := by
    rw [← map_eq_one_iff e.symm e.symm.injective, map_pow, I.onto n hn hp]
    exact exists_congr fun y => ⟨fun h => by rw [h, e.apply_symm_apply], fun h => by rw [← h, e.symm_apply_apply]⟩
  tower n m hn hm hp x := by rw [← map_pow, I.tower n m hn hm hp]
  isom n hn hp x y := hE _ _ _ _ (I.isom n hn hp x y)

theorem exists_tate_iff {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q'] {act : D.O → Q → Q}
    {act' : D.O → Q' → Q'} {E : ℕ → Q → Q → kˣ → Prop} {E' : ℕ → Q' → Q' → kˣ → Prop}
    (e : Q ≃* Q') (ha : ∀ c g, e (act c g) = act' c (e g))
    (hE : ∀ n g g' u, E n g g' u ↔ E' n (e g) (e g') u) (N : ℕ) (l : D.La → Q) (l' : D.La → Q')
    (hl : ∀ y, e (l y) = l' y) :
    (∃ I : TateIsoO D k Q act E, ∀ y, l y = I.ev N y) ↔ (∃ I : TateIsoO D k Q' act' E', ∀ y, l' y = I.ev N y) := by
  constructor
  · rintro ⟨I, hI⟩
    exact ⟨tateTransport I e ha fun n g g' u => (hE n g g' u).1, fun y => by rw [← hl, hI]; rfl⟩
  · rintro ⟨I, hI⟩
    refine ⟨tateTransport I e.symm (fun c g => e.injective (by rw [e.apply_symm_apply, ha, e.apply_symm_apply]))
      (fun n g g' u h => (hE n _ _ u).2 (by rw [e.apply_symm_apply, e.apply_symm_apply]; exact h)), fun y => ?_⟩
    show l y = e.symm (I.ev N y)
    rw [← hI y, ← hl y, e.symm_apply_apply]

variable {R : Type} [CommRing R] (b : Base D R) {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A]
  [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}

theorem lieAt_iff (pb : IsGrpPullback A' A f φ) (act : OActN D.O A) (act' : OActN D.O A')
    (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S') : LieAt b act' β x ↔ LieAt b act β (x ≫ f) := by
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pb (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  have key := fun c r v => GlobalTheory.HTPull.isTanScal_iff pb act act' hact x e he c r v
  constructor
  · intro H v hv
    obtain ⟨w, hw, hvw⟩ := H (e.symm v) ((key _ _ _).2 (by rw [e.apply_symm_apply]; exact hv))
    refine ⟨fun i => e (w i), fun i c => (key _ _ _).1 (hw i c), ?_⟩
    rw [← e.apply_symm_apply v, hvw, map_list_prod, List.map_ofFn]
    rfl
  · intro H v hv
    obtain ⟨w, hw, hvw⟩ := H (e v) ((key _ _ _).1 hv)
    refine ⟨fun i => e.symm (w i), fun i c => (key _ _ _).2 (by rw [e.apply_symm_apply]; exact hw i c),
      e.injective ?_⟩
    rw [hvw, map_list_prod, List.map_ofFn]
    simp [Function.comp_def]

theorem lieRankAt_iff (pb : IsGrpPullback A' A f φ) (act : OActN D.O A) (act' : OActN D.O A')
    (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S') : LieRankAt b act' β x ↔ LieRankAt b act β (x ≫ f) := by
  refine forall_congr' fun k => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun g =>
    forall_congr' fun i => ?_
  have h := GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) S S' A A' f φ (act.toF D) (act'.toF D) pb (fun c => hact _) k
    (spMap g ≫ x) ((g.comp β).comp (b.t i)) D.m
  rwa [Category.assoc] at h

theorem lieHer_iff (pb : IsGrpPullback A' A f φ) (act : OActN D.O A) (act' : OActN D.O A')
    (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S') : LieHer b act' β x ↔ LieHer b act β (x ≫ f) := by
  refine forall_congr' fun R'' => forall_congr' fun _ => forall_congr' fun g => ?_
  have h1 := lieAt_iff b pb act act' hact (g.comp β) (spMap g ≫ x)
  have h2 := lieRankAt_iff b pb act act' hact (g.comp β) (spMap g ≫ x)
  rw [Category.assoc] at h1 h2
  exact and_congr h1 h2

theorem geomAt_iff [IsCommMonObj A] (pb : IsGrpPullback A' A f φ) (act : OActN D.O A) (act' : OActN D.O A')
    (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) (P : LB (G2 A).left) (P' : LB (G2 A').left)
    (hP : P.IsLB) (hP' : P'.IsLB) (φ₂ : (G2 A').left ⟶ (G2 A).left) (sq : IsSquare φ φ₂)
    (H : LBIso P' (P.pull φ₂)) (eta : D.La → (𝟙_ (Over S) ⟶ A)) (eta' : D.La → (𝟙_ (Over S') ⟶ A'))
    (heta : ∀ y, (eta' y).left ≫ φ = f ≫ (eta y).left) (N : ℕ) (k : Type) [Field k] (x : Sp k ⟶ S') :
    GeomAt D N act' P' eta' k x ↔ GeomAt D N act P eta k (x ≫ f) := by
  have dg := SiegelPull.diag_iso sq H
  let e : (Over.mk x ⟶ A') ≃* (Over.mk (x ≫ f) ⟶ A) := MulEquiv.ofBijective (pushHom pb (Over.mk x))
    ⟨SiegelPull.push_injective pb _, SiegelPull.push_surjective pb _⟩
  have hel : ∀ g, (e g).left = g.left ≫ φ := fun g => rfl
  refine exists_tate_iff e (fun c g => GlobalTheory.HTPull.push_comp pb (hact c) _ g) (fun n g g' u => ?_) N _ _
    (fun y => ?_)
  · exact weilIs_grpPullback_of_comm S S' A A' f φ _ _ (pull_isLB hP _) (pull_isLB hP' _) pb dg (Over.mk x) n
      g g' (e g) (e g') _ (hel g) (hel g')
  · apply Over.OverMorphism.ext
    show ((toUnit (Over.mk x)).left ≫ (eta' y).left) ≫ φ = (toUnit (Over.mk (x ≫ f))).left ≫ (eta y).left
    rw [Category.assoc, heta, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
    rfl

end GlobalTheory.HTTransport

namespace GlobalTheory.HTTransport

open ReciprocityTheory.ChartRestriction.G.Pdiv

theorem lieHer_geomAt_iff : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₀ : Scheme.{0}) (A₀ : Over S₀) [GrpObj A₀] [IsCommMonObj A₀] (P₀ : LB (G2 A₀).left), P₀.IsLB → ∀ (X T : Scheme.{0}) (πX : X ⟶ S₀) (z : T ⟶ X) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (AT : Over T) [GrpObj AT] [IsCommMonObj AT] (φX : AX.left ⟶ A₀.left) (φ₂X : (G2 AX).left ⟶ (G2 A₀).left) (φT : AT.left ⟶ A₀.left) (φ₂T : (G2 AT).left ⟶ (G2 A₀).left) (ψ : AT.left ⟶ AX.left) (actX : OActN D.O AX) (actT : OActN D.O AT) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)) (ηT : D.La → (𝟙_ (Over T) ⟶ AT)) (PT : LB (G2 AT).left), PT.IsLB → IsGrpPullback AX A₀ πX φX → IsSquare φX φ₂X → IsGrpPullback AT A₀ (z ≫ πX) φT → IsSquare φT φ₂T → IsGrpPullback AT AX z ψ → ψ ≫ φX = φT → LBIso PT (P₀.pull φ₂T) → (∀ a : D.O, (actT.act a).left ≫ ψ = ψ ≫ (actX.act a).left) → (∀ y, (ηT y).left ≫ ψ = z ≫ (ηX y).left) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), LieHer b actT β x ↔ LieHer b actX β (x ≫ z)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), GeomAt D N actT PT ηT k x ↔ GeomAt D N actX (P₀.pull φ₂X) ηX k (x ≫ z) := by
  intro p _ D R _ b N S₀ A₀ _ _ P₀ hP₀ X T πX z AX _ _ AT _ _ φX φ₂X φT φ₂T ψ actX actT ηX ηT PT hPT _ sqX _ sqT
    pbψ hψ H hact hη
  have w : ((fst AT AT).left ≫ ψ) ≫ AX.hom = ((snd AT AT).left ≫ ψ) ≫ AX.hom := by
    rw [Category.assoc, Category.assoc, pbψ.1.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w]
  let ψ₂ : (G2 AT).left ⟶ (G2 AX).left := pullback.lift _ _ w
  have sqψ : IsSquare ψ ψ₂ := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hcomp : ψ₂ ≫ φ₂X = φ₂T := by
    have h1 : (ψ₂ ≫ φ₂X) ≫ (fst A₀ A₀).left = φ₂T ≫ (fst A₀ A₀).left := by
      rw [Category.assoc, sqX.1, ← Category.assoc, sqψ.1, Category.assoc, hψ, sqT.1]
    have h2 : (ψ₂ ≫ φ₂X) ≫ (snd A₀ A₀).left = φ₂T ≫ (snd A₀ A₀).left := by
      rw [Category.assoc, sqX.2, ← Category.assoc, sqψ.2, Category.assoc, hψ, sqT.2]
    exact Over.tensorObj_ext _ _ h1 h2
  have hB : ((P₀.pull φ₂X).pull ψ₂).IsLB := pull_isLB (pull_isLB hP₀ _) _
  have iso : LBIso PT ((P₀.pull φ₂X).pull ψ₂) :=
    LBIso.trans hPT (pull_isLB hP₀ _) hB H
      (LBIso.chartPull (GlobalTheory.RigidBundleGlue.chartPullComp P₀ φ₂X ψ₂ φ₂T hcomp.symm) (chartPullId _)
        (PullbackComparison.gen_refl _ hB))
  exact ⟨fun R' _ β x => lieHer_iff b pbψ actX actT hact β x,
    fun k _ _ x => geomAt_iff pbψ actX actT hact (P₀.pull φ₂X) PT (pull_isLB hP₀ _) hPT ψ₂ sqψ iso ηX ηT hη N k x⟩

end GlobalTheory.HTTransport
end
end

