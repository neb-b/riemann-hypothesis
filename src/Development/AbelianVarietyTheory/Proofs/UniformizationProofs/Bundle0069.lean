module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0056
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BiTrivLiftOfIsNilpotent
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTrivDeltaAndEvenUnique
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationLiftNilpotent
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDescendThrough
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapDescends
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossIffOfIsActOf
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.CrossTheta

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [gs_eq (r ≫ g) z U h, gs_eq g (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (g ⁻¹ᵁ U) z h _).symm

theorem cross_val {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Y ⟶ X) (b : Y ⟶ Y) {k k' : ℤ}
    (s₁ s₂ : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => k)))
    (s₁' s₂' : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => k')))
    (H : ∀ y J, Good L y J → sval s₁ b y J * sval s₂' (𝟙 _) y J = sval s₂ b y J * sval s₁' (𝟙 _) y J)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval s₁ (r ≫ b) z J * sval s₂' r z J = sval s₂ (r ≫ b) z J * sval s₁' r z J := by
  obtain ⟨I, hI, e⟩ := exists_good L hL (r z) (K := Bool) (fun c => cond c (b ≫ p) (𝟙 _ ≫ p))
    (fun c => J (r ≫ cond c (b ≫ p) (𝟙 _ ≫ p))) (fun a c e => congrArg (fun q => J (r ≫ q)) e)
    (fun c => hJ (r ≫ cond c (b ≫ p) (𝟙 _ ≫ p)))
  have v : ∀ (c : Y ⟶ Y) {m : ℤ} (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => m))),
      I (c ≫ p) = J (r ≫ c ≫ p) → sval s (r ≫ c) z J = (r.stalkMap z).hom (sval s c (r z) I) := by
    intro c m s hc
    rw [sval_of s (r ≫ c) z J (fun _ => I (c ≫ p)) (fun _ => by rw [Category.assoc, hc])]
    exact gs_comp_stalk r c z _ (hI.mem (fun _ : Fin 1 => p) c) _
  have h := congrArg (r.stalkMap z).hom (H (r z) I hI)
  rw [map_mul, map_mul, ← v b s₁ (e true), ← v b s₂ (e true), ← v (𝟙 _) s₁' (e false), ← v (𝟙 _) s₂' (e false),
    Category.comp_id] at h
  exact h

theorem translT_whisker {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (a : A ⟶ A) [IsMonHom a] (x : T ⟶ A) :
    translT A x ≫ T ◁ a = T ◁ a ≫ translT A (x ≫ a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp only [translT, Category.assoc, whiskerLeft_snd, lift_snd, lift_snd_assoc, ThetaPowOrder.translPt_eq,
      MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_fst_assoc]

theorem cross_act {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    (a : A ⟶ A) [IsMonHom a] {k k' : ℤ} (θ : ThetaGrp A L k T) (θ' : ThetaGrp A L k' T) (hp : θ.pt = θ'.pt ≫ a)
    {t₁ t₂ T₁ T₂ : LB.Sec (LPow A L k T)} {t₁' t₂' T₁' T₂' : LB.Sec (LPow A L k' T)}
    (h₁ : IsActOf A L k θ t₁ T₁) (h₂ : IsActOf A L k θ t₂ T₂) (h₁' : IsActOf A L k' θ' t₁' T₁')
    (h₂' : IsActOf A L k' θ' t₂' T₂') :
    (∀ y J, Good L y J → sval (L := L) t₁ (T ◁ a).left y J * sval (L := L) t₂' (𝟙 _) y J =
      sval (L := L) t₂ (T ◁ a).left y J * sval (L := L) t₁' (𝟙 _) y J) ↔
    (∀ y J, Good L y J → sval (L := L) T₁ (T ◁ a).left y J * sval (L := L) T₂' (𝟙 _) y J =
      sval (L := L) T₂ (T ◁ a).left y J * sval (L := L) T₁' (𝟙 _) y J) := by
  have c : (T ◁ a).left ≫ (translT A θ.pt).left = (translT A θ'.pt).left ≫ (T ◁ a).left := by
    rw [← Over.comp_left, ← Over.comp_left, hp, translT_whisker]
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}, Good L z J →
      (sval (L := L) T₁ (r ≫ (T ◁ a).left) z J * sval (L := L) T₂' r z J =
        sval (L := L) T₂ (r ≫ (T ◁ a).left) z J * sval (L := L) T₁' r z J ↔
      sval (L := L) t₁ ((r ≫ (translT A θ'.pt).left) ≫ (T ◁ a).left) z J *
          sval (L := L) t₂' (r ≫ (translT A θ'.pt).left) z J =
        sval (L := L) t₂ ((r ≫ (translT A θ'.pt).left) ≫ (T ◁ a).left) z J *
          sval (L := L) t₁' (r ≫ (translT A θ'.pt).left) z J) := by
    intro Z r z J hJ
    rw [ThetaPowOrder.act_sval h₁ _ z hJ, ThetaPowOrder.act_sval h₂ _ z hJ, ThetaPowOrder.act_sval h₁' _ z hJ,
      ThetaPowOrder.act_sval h₂' _ z hJ, Category.assoc, c, ← Category.assoc, _root_.mul_mul_mul_comm,
      _root_.mul_mul_mul_comm _ (sval (L := L) t₂ _ z J), ← Units.val_mul, Units.mul_right_inj]
  constructor
  · intro H y J hJ
    have h := (key (𝟙 _) y hJ).2 (cross_val hL _ _ t₁ t₂ t₁' t₂' H _ y hJ)
    rwa [Category.id_comp] at h
  · intro H y J hJ
    have h := (key (translT A θ'.pt⁻¹).left y hJ).1 (cross_val hL _ _ T₁ T₂ T₁' T₂' H _ y hJ)
    rwa [← Over.comp_left, ThetaPowOrder.translT_comp, mul_inv_cancel, ThetaPowOrder.translT_one, Over.id_left,
      Category.id_comp] at h

end GlobalTheory.CrossTheta

namespace GlobalTheory

theorem cross_iff_of_isActOf : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (a : A.A ⟶ A.A), IsMonHom a → ∀ (j j' : ℕ) (θ : ThetaGrp A.A A.L (j : ℤ) (TFK (R := R) F)) (θ' : ThetaGrp A.A A.L (j' : ℤ) (TFK (R := R) F)), θ.pt = θ'.pt ≫ a → ∀ (t₁ t₂ T₁ T₂ : SecA A F j) (t₁' t₂' T₁' T₂' : SecA A F j'), IsActOf A.A A.L j θ t₁ T₁ → IsActOf A.A A.L j θ t₂ T₂ → IsActOf A.A A.L j' θ' t₁' T₁' → IsActOf A.A A.L j' θ' t₂' T₂' → (Cross a t₁ t₂ t₁' t₂' ↔ Cross a T₁ T₂ T₁' T₂') := by
  intro _ R _ _ A F _ _ a ha j j' θ θ' hp t₁ t₂ T₁ T₂ t₁' t₂' T₁' T₂' h₁ h₂ h₁' h₂'
  exact CrossTheta.cross_act A.isLB a θ θ' hp h₁ h₂ h₁' h₂'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsConj
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UU.Weight

open GlobalTheory.TorusExt

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

abbrev CompMod (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (α : D.X) : Type :=
  SecMod (fst (TF (R := R) F) D.P.A).left (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))

theorem gs_scal {K : Type} [CommRing K] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of K)) (r : Z ⟶ Y) (z : Z)
    (c : K) : gs r z ⊤ (scal p c) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) :=
  gs_pull r p z ⊤ trivial _

theorem phiRaw_val (hG : GlobalFnsSt) {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))} (hw : w.IsGen) {s s' : Raw D F k}
    (h : PhiRaw D F k 0 g w s s') (α : D.X) (y : (DegPre.BF D F).left) (J) (hJ : Good D.P.L y J) :
    sval (s' α) (𝟙 _) y J = sval (s α) (DegPre.trPt D F g.b).left y J * (uVal D F k α g.b (𝟙 _) y J *
      val (LB.mulGen D.P.L _ _ _ _ (g.s α) w) (fst (TF (R := R) F) D.P.A).left y J).val := by
  obtain ⟨u, hu, hc⟩ := (gen_u D F hG k α (α + 0) g.b (by rw [add_zero, hg.base_pow, _root_.mul_one]) _
    (mulGen_isGen _ _ _ _ _ _ _ (g.isGen α) hw) (fun U _ h => by
    refine (Fintype.prod_sum_type _).trans ?_
    rw [Fin.prod_univ_four, Fin.prod_univ_two]
    show h (cP D _ α * g.b).left ^ (-1 : ℤ) * h (cP D _ α).left ^ (1 : ℤ) * h g.b.left ^ (1 : ℤ) *
      h (1 : TF (R := R) F ⟶ D.P.A).left ^ (-1 : ℤ) *
      (h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h g.b.left ^ (-(k : ℤ))) = _
    simp only [zpow_neg, zpow_one, zpow_natCast]
    ac_rfl)).1
  have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (h α u hu hc) _ (𝟙 _) y J hJ
  have e' := hg.val_phi hG w hw α u hu hc _ (𝟙 _) y J hJ
  rw [Category.id_comp, Over.id_left] at e'
  rw [Category.id_comp] at e
  exact (congrArg (fun β => sval (s' β) (𝟙 _) y J) (add_zero α)).symm.trans
    (e.trans (congrArg (fun q => _ * Units.val q) e'))

theorem phiRaw_smul (hG : GlobalFnsSt) {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))} (hw : w.IsGen)
    {s s' t t' : ∀ α, CompMod D F k α} (h : PhiRaw D F k 0 g w (fun α => (s α).sec) fun α => (s' α).sec)
    (h' : PhiRaw D F k 0 g w (fun α => (t α).sec) fun α => (t' α).sec) (α : D.X) (c : F) (e : s α = c • t α) :
    s' α = c • t' α := by
  refine SecOps.sec_ext (sec_ext_val D.P.isLB fun y J hJ => ?_)
  have a := phiRaw_val hG hg hw h α y J hJ
  have b := phiRaw_val hG hg hw h' α y J hJ
  have t₁ : (DegPre.trPt D F g.b).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ ≫ (fst (TF (R := R) F) D.P.A).left :=
    (congrArg (fun q => q.left) (tr_fst D F g.b)).trans (Category.id_comp _).symm
  change sval (s' α).sec (𝟙 _) y J = sval (c • t' α).sec (𝟙 _) y J
  rw [SecMod.value_smul hJ, a, b, e, SecMod.value_smul hJ, gs_scal, gs_scal, _root_.mul_assoc]
  exact congrArg (fun q => gs q y ⊤ _ * _) t₁

theorem phiRaw_torus (hG : GlobalFnsSt) {k : ℕ} (τ : Multiplicative D.X →* Fˣ) {g : GtPtF D F}
    (hτ : g = torusPt D F (Additive.ofMul τ)) (hg : GtTors D k g)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))} (hw : w.IsGen) :
    ∃ c : Fˣ, ∀ s s' : ∀ α, CompMod D F k α, PhiRaw D F k 0 g w (fun α => (s α).sec) (fun α => (s' α).sec) →
      ∀ α, s' α = ((c * τ (Multiplicative.ofAdd α) : Fˣ) : F) • s α := by
  have hb : g.b = 1 := hτ ▸ torusPt_b _
  obtain ⟨y₀, J₀, hJ₀⟩ := exists_good_chart D F
  obtain ⟨c, hc⟩ := (stalkUnits (F := F) y₀).surjective (val w (𝟙 _) y₀ J₀)
  have vv : ∀ (u : Fˣ) {Z : Scheme.{0}} (r : Z ⟶ (TF (R := R) F).left) (z : Z) J, Good D.P.L z J →
      val (GlobalTheory.UU.scaleGen (unitOn u) (LB.oneGen D.P.L (Y := (TF (R := R) F).left))) r z J = gm r z ⊤ (unitOn u) :=
    fun u Z r z J hJ => (GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans ((congrArg₂ (· * ·) rfl (val_one _)).trans (_root_.mul_one _))
  have hwv : ∀ y J, Good D.P.L y J → val w (𝟙 _) y J = stalkUnits (F := F) y c := fun y J hJ => by
    obtain rfl := pt_eq y₀ y
    refine (val_eq_of_val_eq (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => ?_) hw
      (GlobalTheory.UU.scaleGen_isGen (unitOn c) oneGen_isGen) hJ₀ hJ (hc.symm.trans ((vv c _ _ _ hJ₀).trans (gm_unitOn _ c)).symm)).trans
      ((vv c _ _ _ hJ).trans (gm_unitOn _ c))
    rw [Fin.prod_univ_two, Fintype.prod_empty]
    show h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h g.b.left ^ (-(k : ℤ)) = 1
    rw [hb, zpow_neg, mul_inv_cancel]
  refine ⟨c, fun s s' h α => SecOps.sec_ext (sec_ext_val D.P.isLB fun y J hJ => ?_)⟩
  have cr : LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (g.s α) w)
      (GlobalTheory.UU.scaleGen (unitOn (c * τ (Multiplicative.ofAdd α))) (LB.oneGen D.P.L (Y := (TF (R := R) F).left))) :=
    corr_of_val D.P.isLB fun y J hJ => by
      have e : charVal g α y J = stalkUnits (F := F) y (τ (Multiplicative.ofAdd α)) := hτ ▸ torusPt_val τ α hJ
      refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) e (hwv y J hJ))).trans
        (Eq.trans ?_ ((vv _ _ _ _ hJ).trans (gm_unitOn _ _)).symm)
      exact (mul_comm _ _).trans (map_mul (stalkUnits (F := F) y) _ _).symm
  have C : IsCub (th D (T := DegPre.BF D F) y J) := isCub_cubV D.cub hJ
  have u₁ : uVal D F k α g.b (𝟙 _) y J = 1 := by
    rw [uVal_id, hb, MonObj.comp_one, C.face₃, inv_one, _root_.mul_one]
    exact Finset.prod_eq_one fun _ _ => C.face₂ _ _
  have t₁ : DegPre.trPt D F g.b = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [tr_fst, Category.id_comp]
    · rw [tr_pr, hb, MonObj.comp_one, _root_.mul_one, Category.id_comp]
  have a := phiRaw_val hG hg hw h α y J hJ
  rw [u₁, _root_.one_mul, t₁, Over.id_left, (val_corr hJ cr _).trans (vv _ _ _ _ hJ)] at a
  change sval (s' α).sec (𝟙 _) y J = sval (((c * τ (Multiplicative.ofAdd α) : Fˣ) : F) • s α).sec (𝟙 _) y J
  rw [SecMod.value_smul hJ, gs_scal, Category.id_comp, mul_comm]
  exact a.trans (congrArg _ (gs_unit _ y ⊤ trivial _).symm)

theorem exists_conj {K K' E M : Type} [CommRing K] [CommRing K'] [AddCommGroup E] [Module K E] [AddCommGroup M]
    [Module K' M] (σ : K ≃+* K') (j : E ≃+ M) (hj : ∀ (c : K) v, j (c • v) = σ c • j v) (Φ : M ≃ₗ[K'] M) :
    ∃ Ψ : E ≃ₗ[K] E, ∀ v, j (Ψ v) = Φ (j v) :=
  ⟨{ j.trans (Φ.toAddEquiv.trans j.symm) with
      map_smul' := fun c v => j.injective (by
        show j (j.symm (Φ (j (c • v)))) = j (c • j.symm (Φ (j v)))
        rw [hj, hj, map_smul, j.apply_symm_apply, j.apply_symm_apply]) }, fun _ => j.apply_symm_apply _⟩

abbrev TorsPt {S : Scheme.{0}} (P : PolAV S) (T : Over S) (N : ℕ) : Subgroup (T ⟶ P.A) :=
  (powMonoidHom N : (T ⟶ P.A) →* (T ⟶ P.A)).ker

theorem exists_projective_rep (hL : Laws) (hL₂ : Laws2) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S)
    {F : Type} [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) {N : ℕ} (hN : (N : F) ≠ 0) :
    ∃ (Φ : TorsPt P (Over.mk p) N → (SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L N (Over.mk p)) ≃ₗ[F]
        SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L N (Over.mk p))))
      (e : TorsPt P (Over.mk p) N → TorsPt P (Over.mk p) N → Fˣ),
      Module.finrank F (SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L N (Over.mk p))) = N ^ P.g ∧
      (∀ a, ∃ θ : ThetaGrp P.A P.L N (Over.mk p), θ.pt = a.1 ∧ ∀ v, IsActOf P.A P.L N θ v.sec (Φ a v).sec) ∧
      (∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v)) ∧
      (∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) ∧ ∀ a, (∀ b, e a b = 1) → a = 1 := by
  obtain ⟨Φ, e, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.ThetaRep.exists_projective_rep hL hL₂ S P F p N hN
  let σ : F ≃+* Γ((Over.mk p).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv
  let j : SecMod (F := F) (fst (Over.mk p) P.A).left (LPow P.A P.L N (Over.mk p)) ≃+ SecM P.A P.L N (Over.mk p) :=
    { toFun := fun v => SecM.ofSec P.A v.sec
      invFun := fun v => SecMod.mk _ (SecM.toSec P.A v)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hj : ∀ (c : F) v, j (c • v) = σ c • j v := fun _ _ => rfl
  let u : Γ((Over.mk p).left, ⊤)ˣ ≃* Fˣ := Units.mapEquiv σ.symm.toMulEquiv
  have hu : ∀ r, σ (u r : F) = r.val := fun r => σ.apply_symm_apply _
  have hd := (congrArg Cardinal.toNat (rank_eq_of_equiv_equiv σ j σ.bijective hj)).trans h₁
  choose Ψ hΨ using fun a : TorsPt P (Over.mk p) N => exists_conj σ j hj (Φ a)
  refine ⟨Ψ, fun a b => u (e a b), hd, fun a => ?_, fun a b => ?_, fun a b v => ?_,
    fun a h => Subtype.ext (h₅ a fun b => u.injective ((h b).trans (map_one u).symm))⟩
  · obtain ⟨θ, h, h'⟩ := h₂ a
    refine ⟨θ, h, fun v => ?_⟩
    have := h' (j v)
    rw [← hΨ] at this
    exact this
  · obtain ⟨r, hr⟩ := h₃ a b (a * b : TorsPt P (Over.mk p) N) rfl
    refine ⟨u r, fun v => j.injective ?_⟩
    rw [hj, hΨ, hΨ, hΨ, hu]
    exact hr (j v)
  · apply j.injective
    beta_reduce
    rw [hj, hΨ, hΨ, hΨ, hΨ]
    exact ((h₄ a b).2 (j v)).trans (congrArg (fun c => c • Φ b (Φ a (j v))) (hu (e a b)).symm)

end GlobalTheory.UU.Weight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenPull
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.TowerEx

theorem toBase_mul {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) (hw : F ≫ G.hom = G'.hom ≫ f) (T : Over S') (x y : T ⟶ G') :
    toBase hw (x * y) = toBase hw x * toBase hw y :=
  Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

theorem exists_congr {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {P : CP G} {P' : CP G'} {f f' : S' ⟶ S} {F F' : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) (e : f = f') (e' : F = F') (hw') : ∃ w', IsCPMap P' P f' F' hw' w' := by
  subst e e'
  exact ⟨w, h⟩

theorem exists_cancel {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] {P : CP G} {P' : CP G'} {P'' : CP G''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {f'' : S'' ⟶ S} {F : G'.left ⟶ G.left} {F' : G''.left ⟶ G'.left} {F'' : G''.left ⟶ G.left}
    {hw w hw'' w''} (h : IsCPMap P' P f F hw w) (h'' : IsCPMap P'' P f'' F'' hw'' w'')
    (hF : IsGrpPullback G'' G' f' F') (e : f' ≫ f = f'') (e' : F' ≫ F = F'') :
    ∃ w', IsCPMap P'' P' f' F' hF.1.w w' := by
  subst e e'
  exact ((isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF.1.w _ h).2 (toBase_mul hF _) _ h'').imp fun _ => And.left

theorem exists_even_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {P : CP G} {P' : CP G'} {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'}
    [IsMonHom i'] (hi : TorusCompat f F i' i) (σ : CubTriv P.c i) (hσ : σ.Even) :
    ∃ σ' : CubTriv P'.c i', σ'.Even := by
  have hE := SplitTorus.isGrpPullback_bcMap f X
  rw [torusCompat_iff] at hi
  have hc : ∀ k : Fin 2, ![i'.left, (1 : splitTorus S' X ⟶ G').left] k ≫ F =
      SplitTorus.bcMap f X ≫ ![i.left, (1 : splitTorus S X ⟶ G).left] k := fun k => by
    fin_cases k
    · exact hi.symm
    · show (1 : splitTorus S' X ⟶ G').left ≫ F = SplitTorus.bcMap f X ≫ (1 : splitTorus S X ⟶ G).left
      rw [one_left_comp h.mul, one_left, ← Category.assoc, hE.1.w]
  obtain ⟨s, hs, Hs⟩ := CubTransport.exists_pmaps ((isGen_iff w).1 h.gen) P.L.isLB P'.L.isLB _ hc σ.s σ.gen
  let β := toBaseHom (toBase_mul hE hE.1.w)
  have hβ : ∀ {T : Over S'} (t : T ⟶ splitTorus S' X), β T t ≫ i = toBase hw (t ≫ i') := fun t =>
    Over.OverMorphism.ext (by
      show (t.left ≫ SplitTorus.bcMap f X) ≫ i.left = (t.left ≫ i'.left) ≫ F
      rw [Category.assoc, hi, Category.assoc])
  have vs : ∀ (T : Over S') (z : T.left) (J') (J), Good P'.L.L z J' → Good P.L.L z J →
      ∀ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left)) →
      ∀ t : T ⟶ splitTorus S' X, @id (T.left.presheaf.stalk z)ˣ (val σ.s (β T t).left z J) =
        W (t ≫ i') * (W 1)⁻¹ * val s t.left z J' := by
    intro T z J' J hJ' hJ W hW t
    refine (CubTransport.val_pmaps hc Hs t.left hJ hJ').trans (congrArg₂ (· * ·) ?_ rfl)
    rw [hW, hW]
    exact CubTrivTorus.prod_cubTriv i' t (fun q => gw w q z (J (q ≫ F)) (J' q))
  refine ⟨⟨s, hs, fun T x y u z J' hJ' => ?_⟩, fun T x z J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left) := ⟨_, fun _ => rfl⟩
    have a := (h.vals T z J' J hJ' hJ W hW).2.2 (x ≫ i') (y ≫ i') (u ≫ i')
    obtain ⟨Z, hZ⟩ : ∃ Z : (T ⟶ splitTorus S' X) → (T.left.presheaf.stalk z)ˣ,
      ∀ t, Z t = val σ.s (β T t).left z J := ⟨_, fun _ => rfl⟩
    have b := σ.cub _ (β T x) (β T y) (β T u) z J hJ
    simp only [← map_mul, hβ] at b
    have b' : Z (x * y * u) * Z x * Z y * Z u = @id (T.left.presheaf.stalk z)ˣ
        (cubV P.c (T := Over.mk (T.hom ≫ f)) z J (toBase hw (x ≫ i')) (toBase hw (y ≫ i')) (toBase hw (u ≫ i'))) *
        Z (x * y) * Z (x * u) * Z (y * u) := by
      simp only [hZ]; exact b
    have v : ∀ t, Z t = W (t ≫ i') * (W 1)⁻¹ * val s t.left z J' := fun t => (hZ t).trans (vs T z J' J hJ' hJ W hW t)
    generalize @id (T.left.presheaf.stalk z)ˣ
        (cubV P.c (T := Over.mk (T.hom ≫ f)) z J (toBase hw (x ≫ i')) (toBase hw (y ≫ i')) (toBase hw (u ≫ i'))) = C
      at a b'
    simp only [v, MonObj.mul_comp] at b'
    apply Additive.ofMul.injective
    have a' := congrArg Additive.ofMul a
    have b'' := congrArg Additive.ofMul b'
    simp only [ofMul_mul, ofMul_inv] at a' b'' ⊢
    linear_combination (norm := abel) a' + b''
  · obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w x.left z (J (x.left ≫ F)) (J' x.left) := ⟨_, fun _ => rfl⟩
    have a := (h.vals T z J' J hJ' hJ W hW).2.1 (x ≫ i')
    have b := hσ _ (β T x) z J hJ
    rw [← map_inv, hβ] at b
    have b' : W (x⁻¹ ≫ i') * (W 1)⁻¹ * val s (x⁻¹).left z J' =
        val P.sym ((x ≫ i').left ≫ F) z J * (W (x ≫ i') * (W 1)⁻¹ * val s x.left z J') := by
      rw [← vs T z J' J hJ' hJ W hW, ← vs T z J' J hJ' hJ W hW]; exact b
    rw [GrpObj.inv_comp] at b'
    show val s _ z J' = _ * val s _ z J'
    apply Additive.ofMul.injective
    have a' := congrArg Additive.ofMul a
    have b'' := congrArg Additive.ofMul b'
    simp only [ofMul_mul, ofMul_inv] at a' b'' ⊢
    linear_combination (norm := abel) a' + b''

theorem nonempty_biTriv (A : Type) [CommRing A] [IsLocalRing A] (hA : IsNilpotent (IsLocalRing.maximalIdeal A))
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (P : CP G) (i : splitTorus _ X ⟶ G)
    (hi : IsMonHom i) : Nonempty (BiTriv P.c i) := by
  letI : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  let f := red (IsLocalRing.maximalIdeal A)
  have hF := isGrpPullback_pullback G f
  have : Smooth ((Over.pullback f).obj G).hom := by show Smooth (pullback.snd G.hom f); infer_instance
  have : GeometricallyConnected ((Over.pullback f).obj G).hom := by
    show GeometricallyConnected (pullback.snd G.hom f); infer_instance
  have : ConnectedSpace (Spec (CommRingCat.of (A ⧸ IsLocalRing.maximalIdeal A))) :=
    SplitTorus.connectedSpace_of_isLocalRing _
  have := (GroupConn.connectedSpace_group _ ((Over.pullback f).obj G)).1
  obtain ⟨i₀, h₀, -⟩ := existsUnique_torusCompat (G' := (Over.pullback f).obj G) hF.1 i
  obtain ⟨_, _, _, _, _, _, _, hP⟩ := exists_isCPMap P (toBase_mul hF hF.1.w) _ (pull_isLB P.L.isLB _) _
    (pullIso_isGen P.L.isLB _)
  exact _root_.GlobalTheory.UU.biTriv_lift_of_isNilpotent A _ hA X G _ _ _ hF P _ _ hP i i₀ hi (h₀.isMonHom hF) h₀
    (BiextTriv.main _ X _ _ _ i₀ (h₀.isMonHom hF))

theorem nonempty_desc (A : Type) [CommRing A] [IsLocalRing A] (hA : IsNilpotent (IsLocalRing.maximalIdeal A))
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (P : CP G) (Q : TQ G X)
    (h : ∃ σ : CubTriv P.c Q.i, σ.Even) : Nonempty (Q.Desc P) := by
  have : ConnectedSpace (Spec (CommRingCat.of A)) := SplitTorus.connectedSpace_of_isLocalRing _
  have := (GroupConn.connectedSpace_group _ G).1
  exact UU.nonempty_desc _ X G Q P (nonempty_biTriv A hA G P Q.i Q.i_hom) h

theorem exists_lift {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] [Nontrivial A']
    (hA : IsNilpotent (IsLocalRing.maximalIdeal A)) (φ : A →+* A') (hφ : Function.Surjective φ)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (G' : Over (Spec (CommRingCat.of A'))) [GrpObj G']
    [IsCommMonObj G'] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom φ)) F)
    {P : CP G} {P' : CP G'} {hw} {w} (hP : IsCPMap P' P (Spec.map (CommRingCat.ofHom φ)) F hw w) (Q' : TQ G' X)
    (h : ∃ σ : CubTriv P'.c Q'.i, σ.Even) :
    ∃ Q : TQ G X, TorusCompat (Spec.map (CommRingCat.ofHom φ)) F Q'.i Q.i ∧ ∃ σ : CubTriv P.c Q.i, σ.Even := by
  have hJ : RingHom.ker φ ≠ ⊤ := RingHom.ker_ne_top φ
  have hN : IsNilpotent (RingHom.ker φ) := by
    obtain ⟨n, hn⟩ := hA
    exact ⟨n, le_bot_iff.1 ((Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal hJ) n).trans hn.le)⟩
  let e := (RingHom.quotientKerEquivOfSurjective hφ).symm
  let g : Spec (CommRingCat.of (A ⧸ RingHom.ker φ)) ⟶ Spec (CommRingCat.of A') := Spec.map e.toCommRingCatIso.hom
  have hg : g ≫ Spec.map (CommRingCat.ofHom φ) = red (RingHom.ker φ) := by
    rw [← Spec.map_comp]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => ?_))
    exact (RingHom.quotientKerEquivOfSurjective hφ).symm_apply_eq.2 rfl
  have hG := isGrpPullback_pullback G' g
  have hF₀ := (hG.comp hF).congr hg rfl
  obtain ⟨Q₀, h₀⟩ := exists_tq_baseChange _ _ g X G' _ _ hG Q'
  obtain ⟨Q, hQ⟩ := TorusQuotLift.main A _ hN X G _ _ hF₀ Q₀
  refine ⟨Q, ?_, ?_⟩
  · have : IsIso (SplitTorus.bcMap g X) := (SplitTorus.isGrpPullback_bcMap g X).1.isIso_fst_of_isIso
    rw [torusCompat_iff] at h₀ hQ ⊢
    rw [← cancel_epi (SplitTorus.bcMap g X), ← Category.assoc, ← bcMap_comp, hg, hQ, ← Category.assoc, ← h₀,
      Category.assoc]
  · obtain ⟨_, _, _, _, _, _, _, hP₀⟩ := exists_isCPMap P' (toBase_mul hG hG.1.w) _ (pull_isLB P'.L.isLB _) _
      (pullIso_isGen P'.L.isLB _)
    obtain ⟨_, -, h₁⟩ := hP.exists_comp hP₀ (hG.comp hF).1.w
    obtain ⟨_, h₂⟩ := exists_congr h₁ hg rfl hF₀.1.w
    obtain ⟨σ, hσ⟩ := h
    have := Q₀.i_hom
    exact _root_.GlobalTheory.CubeLift.exists_even_cubTriv A _ hN hJ X G _ _ _ hF₀ P _ _ h₂ Q.i Q₀.i Q.i_hom Q₀.i_hom hQ
      (nonempty_biTriv A hA G P Q.i Q.i_hom) (exists_even_pull hP₀ h₀ σ hσ)

theorem exists_transition {S S' : Scheme.{0}} [ConnectedSpace S'] {f : S' ⟶ S} {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    [ConnectedSpace G'.left] {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {P : CP G} {P' : CP G'} {hw} {w}
    (hP : IsCPMap P' P f F hw w) {Q : TQ G X} {Q' : TQ G' X} (h : TorusCompat f F Q'.i Q.i) (D : Q.Desc P)
    (D' : Q'.Desc P') :
    ∃ β : Q'.B.left ⟶ Q.B.left, IsCPPullback D'.M D.M f β ∧ Q'.q.left ≫ β = F ≫ Q.q.left := by
  obtain ⟨β, hq, hβ⟩ := TQ.exists_isGrpPullback _ _ f X G G' F hF Q Q' h
  obtain ⟨_, -, h₁⟩ := D.map.exists_comp hP (by rw [Category.assoc, Over.w, Category.comp_id, hw])
  obtain ⟨_, h₂⟩ := exists_congr h₁ (Category.comp_id f) hq.symm (by
    rw [Category.assoc, hβ.1.w, ← Category.assoc, Over.w])
  exact ⟨β, ⟨hβ, isCPMap_descends _ _ f X G' Q' P' D' Q.B D.M β hβ.1.w _ _ (toBase_mul hβ _) h₂⟩, hq⟩

end GlobalTheory.UU.TowerEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Imports
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.NullExp

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (σ : U.SecGT T k) (f : ∀ α, SecBT D T k α), U.ExpT T k σ f → NullFam I f := by
  intro R _ _ I D A G _ _ U T k σ f H e
  obtain ⟨s, hs⟩ := H e
  refine ⟨s, fun α hα Z r hr z J hJ => ?_⟩
  refine GlobalTheory.LiftTest.main R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) _ D.P.L D.P.isLB _ _ _ (f α)
    ?_ Z r hr z J hJ
  intro Z x r hx z J hJ
  have hc : (r ≫ (fst T D.P.A).left) ≫ T.hom = (x ≫ (fstG I e G).left) ≫ G.hom := by
    rw [Category.assoc, Category.assoc, Over.w (fst T D.P.A), Over.w (fstG I e G), ← Over.w (snd T D.P.A),
      ← Category.assoc, hx, Category.assoc, Over.w (U.gt e).pG]
  let rG : Z ⟶ (T ⊗ G).left := pullback.lift (r ≫ (fst T D.P.A).left) (x ≫ (fstG I e G).left) hc
  choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
  exact (hs Z x rG r (pullback.lift_snd _ _ _) hx (pullback.lift_fst _ _ _).symm z JG J hJG hJ).1 α hα

end GlobalTheory.NullExp
end

