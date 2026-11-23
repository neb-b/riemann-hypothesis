module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0022
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0019
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsFrameGCoefficientRingBaseChange
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TripleFrameBaseChange

open MvPolynomial (X C)

theorem spec_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem gm_unit_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) {Z : Scheme.{0}} (r : Z ⟶ Sp B)
    (z : Z) : gm r z ⊤ (unitΓ (Units.map f.toMonoidHom u)) = gm (r ≫ spMap f) z ⊤ (unitΓ u) := by
  refine Eq.trans ?_ (gm_pull r (spMap f) z ⊤ trivial (unitΓ u))
  refine congrArg (gm r z ⊤) (Units.ext ?_)
  exact congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}

theorem val_scale {Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) (c : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (scaleGenG t φ ε c g) r z J = gm r z ⊤ c * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0)

def jetOver (d m n : ℕ) : jOG (spMap ψ ≫ x0) d m n ⟶ jOG x0 d m n :=
  Over.homMk (spMap (jetBC ψ (Fin n × Fin d) m)) (by
    dsimp
    simp only [spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext s
    exact jetBC_algebraMap ψ _ m s)

theorem psIn_map {d n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (f : MvPowerSeries (Fin n × Fin d) S) :
    psIn d m r (MvPowerSeries.map ψ f) = MvPolynomial.map ψ (psIn d m r f) := by
  unfold psIn
  rw [MvPolynomial.map_rename]
  congr 1
  unfold psTrunc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem subst_square {n n' d : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) :
    homAt (spMap ψ ≫ x0) (jetSubstP m (fun i => MvPolynomial.map ψ (φ i)) :
        Jet S' (Fin n × Fin d) m →ₐ[S'] Jet S' (Fin n' × Fin d) m) ≫ jetOver ψ x0 d m n =
      jetOver ψ x0 d m n' ≫ homAt x0 (jetSubstP m φ : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ m) = spMap (jetBC ψ _ m) ≫ spMap _
  rw [spec_comp, spec_comp]
  exact congrArg spMap (PullbackSections.jetSubstP_comp_jetBC ψ m φ)

theorem jetMap_congr {R κ κ' : Type} [CommRing R] {m : ℕ} {f g : κ → MvPolynomial κ' R} (e : f = g)
    (hf : ∀ i, f i ∈ orig R κ') (hg : ∀ i, g i ∈ orig R κ') : jetMap (m := m) f hf = jetMap (m := m) g hg := by
  subst e
  rfl

theorem copy_square (d m n : ℕ) (i : Fin n) :
    homAt (spMap ψ ≫ x0) (jetCopy d m i : Jet S' (Fin 1 × Fin d) m →ₐ[S'] Jet S' (Fin n × Fin d) m) ≫
        jetOver ψ x0 d m 1 =
      jetOver ψ x0 d m n ≫ homAt x0 (jetCopy d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ m) = spMap (jetBC ψ _ m) ≫ spMap _
  rw [spec_comp, spec_comp]
  have e := PullbackSections.jetMap_comp_jetBC ψ m (fun p : Fin 1 × Fin d => (X (i, p.2) : MvPolynomial (Fin n × Fin d) S))
    (fun _ => X_mem_orig _) (fun p => by rw [MvPolynomial.map_X]; exact X_mem_orig _)
  rw [jetMap_congr (show (fun p : Fin 1 × Fin d => MvPolynomial.map ψ (X (i, p.2) : MvPolynomial (Fin n × Fin d) S)) =
    fun p => X (i, p.2) from funext fun p => MvPolynomial.map_X ψ _) _ (fun _ => X_mem_orig _)] at e
  exact congrArg spMap e

variable {ψ x0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {x' : ∀ m, jOG (spMap ψ ≫ x0) d m 1 ⟶ t.G}

theorem point_bc (hx : ∀ m, x' m = jetOver ψ x0 d m 1 ≫ x m) {n : ℕ} (m : ℕ) (i : Fin n) :
    jptG t (spMap ψ ≫ x0) d x' m i = jetOver ψ x0 d m n ≫ jptG t x0 d x m i := by
  unfold jptG
  rw [hx m, ← Category.assoc, copy_square, Category.assoc]

variable {e : ∀ m, FrTyG t x0 d x m} {e' : ∀ m, FrTyG t (spMap ψ ≫ x0) d x' m} {m : ℕ}
  (hc : LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L
    (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m) (jetOver ψ x0 d m 2).left))
  {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J)
include hc hJ

theorem val_subst {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S)
    (φ' : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S') (hφ : ∀ i j, φ' i j = MvPolynomial.map ψ (φ i j))
    (r : Z ⟶ (jOG (spMap ψ ≫ x0) d m n).left) :
    val (peG t (spMap ψ ≫ x0) d x' e' m φ') r z J = val (peG t x0 d x e m φ) (r ≫ (jetOver ψ x0 d m n).left) z J := by
  obtain rfl : φ' = fun i j => MvPolynomial.map ψ (φ i j) := funext fun i => funext fun j => hφ i j
  refine (val_pull hJ _ _ _).trans ((val_corr hJ hc _).trans ((val_pull hJ _ _ _).trans
    (Eq.trans ?_ (val_pull hJ _ _ _).symm)))
  rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left,
    subst_square ψ x0 m (fun p : Fin 2 × Fin d => φ p.1 p.2)]

end GlobalTheory.TripleFrameBaseChange

namespace GlobalTheory

open TripleFrameBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X C)

theorem isFrameG_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t x1 d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m)))) → ∀ (F : Fin d → PS S 2 d) (act : 𝓞 E → Fin d → PS S 1 d) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d) (ad : 𝓞 E → PS S 2 d), IsFrameG t x0 d x F act ph1 ph2 sy ad e → IsFrameG t x1 d x' (fun i => (MvPowerSeries.map ψ (F i))) (fun a i => (MvPowerSeries.map ψ (act a i))) (MvPowerSeries.map ψ ph1) (MvPowerSeries.map ψ ph2) (MvPowerSeries.map ψ sy) (fun a => (MvPowerSeries.map ψ (ad a))) e' := by
  intro E _ _ _ H X0 t S S' _ _ ψ x0 x1 h01 d x x' hx0 e e' _ he' hc0 F act ph1 ph2 sy ad h
  subst h01
  have hx : ∀ m, x' m = jetOver ψ x0 d m 1 ≫ x m := fun m => Over.OverMorphism.ext (hx0 m)
  have hc : ∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L
      (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m) (jetOver ψ x0 d m 2).left) := hc0
  have hX : ∀ {n : ℕ} (p : Fin n × Fin d), (X p : MvPolynomial (Fin n × Fin d) S') = MvPolynomial.map ψ (X p) :=
    fun p => (MvPolynomial.map_X ψ p).symm
  refine ⟨he', fun m => ?_, fun m => ?_, fun m => ?_, fun a => ?_⟩
  · obtain ⟨u, hu, hcor⟩ := h.ph1 m
    refine ⟨Units.map (jetBC ψ _ m).toMonoidHom u, (congrArg (jetBC ψ _ m) hu).trans (PullbackSections.jetBC_psJet ψ m ph1),
      corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    have k := val_corr hJ hcor (𝟙 _ ≫ (jetOver ψ x0 d m 3).left)
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_pull hJ _ _ _).symm.trans (k.trans ?_)))
    · rw [point_bc hx, point_bc hx, point_bc hx, ← comp_lift, ← comp_lift, Over.comp_left, Category.assoc]
    · refine (val_scale hJ _ _ _).trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)
      refine congrArg₂ (· * ·) (gm_unit_map _ u _ y).symm ?_
      refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
      · exact (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => psIn_map ψ m _ _, fun j => hX _⟩) _).symm
      refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
      all_goals
        exact (val_inv _ _).trans ((congrArg (·⁻¹)
          (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => hX _⟩) _).symm).trans
          (val_inv _ _).symm)
  · obtain ⟨u, hu, hcor⟩ := h.ph2 m
    refine ⟨Units.map (jetBC ψ _ m).toMonoidHom u, (congrArg (jetBC ψ _ m) hu).trans (PullbackSections.jetBC_psJet ψ m ph2),
      corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    have k := val_corr hJ hcor (𝟙 _ ≫ (jetOver ψ x0 d m 3).left)
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_pull hJ _ _ _).symm.trans (k.trans ?_)))
    · rw [point_bc hx, point_bc hx, point_bc hx, ← comp_lift, ← comp_lift, Over.comp_left, Category.assoc]
    · refine (val_scale hJ _ _ _).trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)
      refine congrArg₂ (· * ·) (gm_unit_map _ u _ y).symm ?_
      refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
      · exact (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => psIn_map ψ m _ _⟩) _).symm
      refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
      all_goals
        exact (val_inv _ _).trans ((congrArg (·⁻¹)
          (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => hX _⟩) _).symm).trans
          (val_inv _ _).symm)
  · obtain ⟨u, hu, hcor⟩ := h.sy m
    refine ⟨Units.map (jetBC ψ _ m).toMonoidHom u, (congrArg (jetBC ψ _ m) hu).trans (PullbackSections.jetBC_psJet ψ m sy),
      corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    have k := val_corr hJ hcor (𝟙 _ ≫ (jetOver ψ x0 d m 2).left)
    refine (val_corr hJ (hc m) _).trans ((val_pull hJ _ _ _).trans (k.trans ?_))
    refine (val_scale hJ _ _ _).trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)
    refine congrArg₂ (· * ·) (gm_unit_map _ u⁻¹ _ y).symm ?_
    exact (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => hX _⟩) _).symm
  · obtain ⟨wL, hw, hall⟩ := h.ad a
    refine ⟨wL, hw, fun m => ?_⟩
    obtain ⟨u, hu, hcor⟩ := hall m
    refine ⟨Units.map (jetBC ψ _ m).toMonoidHom u, (congrArg (jetBC ψ _ m) hu).trans (PullbackSections.jetBC_psJet ψ m (ad a)),
      corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    have k := val_corr hJ hcor (𝟙 _ ≫ (jetOver ψ x0 d m 2).left)
    refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) ((val_mul hJ _ _ _).symm.trans (k.trans ?_)))
    · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      rw [point_bc hx, point_bc hx, ← comp_lift, Over.comp_left, Category.assoc]
    · exact val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => psIn_map ψ m _ _, fun j => hX _⟩) _
    · refine (val_scale hJ _ _ _).trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)
      refine congrArg₂ (· * ·) (gm_unit_map _ u _ y).symm ?_
      exact (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => psIn_map ψ m _ _⟩) _).symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.LocallyOfFiniteTypePullbackUnit
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetSer

theorem mem_sup_pow_of_toJet_mem_map {R : Type} [CommRing R] {κ : Type} [Finite κ] (m : ℕ)
    (I : Ideal (MvPowerSeries κ R)) (g : MvPowerSeries κ R) (hg : toJet m g ∈ I.map (toJetHom R κ m)) :
    g ∈ I ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ R)) ^ (m + 1) := by
  have hs : Function.Surjective (toJetHom R κ m) := fun q => by
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨P, toJet_coe m P⟩
  obtain ⟨h, hh, e⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 hg
  have h2 : g - h ∈ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ R)) ^ (m + 1) := by
    rw [← germIdeal_eq_span, mem_germIdeal_pow_iff]
    intro d hd
    rw [map_sub, (toJet_eq_iff m h g).1 e d hd, sub_self]
  have : g = h + (g - h) := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mem_sup_left hh) (Ideal.mem_sup_right h2)

theorem locallyOfFiniteType_pullback_unit {S : Scheme.{0}} (G : Over S) [GrpObj G] [LocallyOfFiniteType G.hom]
    (f : G ⟶ G) : LocallyOfFiniteType (pullback f η[G]).hom := by
  have h1 : LocallyOfFiniteType (f.left ≫ G.hom) := by rw [Over.w f]; infer_instance
  have h2 : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left G.hom
  have h3 := (IsPullback.of_hasPullback f η[G]).map (Over.forget S)
  have h4 : LocallyOfFiniteType (pullback.snd f η[G]).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h3 h2
  have h5 : (pullback f η[G]).hom = (pullback.snd f η[G]).left := by
    rw [← Over.w (pullback.snd f η[G])]
    exact Category.comp_id _
  rw [h5]
  exact h4

theorem exists_pow_le_span_sup_pow_succ : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] (f : G ⟶ G), η[G] ≫ f = η[G] → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Spec (CommRingCat.of k)), Finite {x : Over.mk t ⟶ G // x ≫ f = 1}) → ∀ (d : ℕ) (x : GlobalTheory.JetSer.Fam G (Fin d)), Chart.IsUnivChart G d x → ∀ φ : Pt k 1 d, GlobalTheory.JetSer.IsMapOf x x f φ → ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS k 1 d)) ^ M ≤ Ideal.span (Set.range φ) ⊔ Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS k 1 d)) ^ (M + 1) := by
  intro k _ G _ _ f hf hfin d x hx φ hφ
  haveI := locallyOfFiniteType_pullback_unit G f
  have hext : ∀ {T : Over (Spec (CommRingCat.of k))} (u v : T ⟶ pullback f η[G]),
      u ≫ pullback.fst f η[G] = v ≫ pullback.fst f η[G] → u = v := fun u v h =>
    pullback.hom_ext h (toUnit_unique _ _)
  have hfinK : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Spec (CommRingCat.of k)),
      Finite (Over.mk t ⟶ pullback f η[G]) := by
    intro Ω _ _ t
    haveI := hfin Ω t
    refine Finite.of_injective (β := {x : Over.mk t ⟶ G // x ≫ f = 1})
      (fun u => ⟨u ≫ pullback.fst f η[G], ?_⟩) (fun u v h => hext u v (congrArg Subtype.val h))
    rw [Category.assoc, pullback.condition, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  have h1f : (1 : Chart.sp (R₀ := k) k ⟶ G) ≫ f = toUnit _ ≫ η[G] := by
    rw [Hom.one_def, Category.assoc, hf]
  obtain ⟨A, _, _, aug, M, io, hM, hio, hU⟩ :=
    GlobalTheory.T.exists_universal_thickening_of_finite_points k (pullback f η[G]) hfinK (pullback.lift 1 (toUnit _) h1f)
  refine ⟨M + 1, ?_⟩
  obtain ⟨hex, -, hfp, -, -⟩ := repSt_of_jetAlgSt jetAlg k G d x hx (Fin 1 × Fin d)
  obtain ⟨y, hy, -⟩ := hex (pt k (n := 1) d 0) (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt 0)
  have hy' := hφ.2 1 _ y hy
  rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_comp1_pt_right] at hy'
  obtain ⟨ψ₀, hψ₀, hy₀⟩ := hy.2 (M + 1)
  obtain ⟨ψ₁, hψ₁, hy₁⟩ := hy'.2 (M + 1)
  have hya := (hfp _ y hy).2 (M + 1)
  have hxa := (isFPt_of_isUnivChart hx).2 (M + 1)
  set I : Ideal (Chart.JetR k (Fin 1 × Fin d) (M + 1)) :=
    (Ideal.span (Set.range φ)).map (toJetHom k (Fin 1 × Fin d) (M + 1)) with hI
  have hIle : I ≤ RingHom.ker (Chart.jetAug k (Fin 1 × Fin d) (M + 1)) := by
    rw [hI, Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact (jetAug_toJet (M + 1) (φ j)).trans (hφ.1 j)
  let π := Ideal.Quotient.mkₐ k I
  let augQ : (Chart.JetR k (Fin 1 × Fin d) (M + 1) ⧸ I) →ₐ[k] k :=
    Ideal.Quotient.liftₐ I (Chart.jetAug k (Fin 1 × Fin d) (M + 1)) (fun a ha => hIle ha)
  have haπ : augQ.comp π = Chart.jetAug k (Fin 1 × Fin d) (M + 1) := AlgHom.ext fun _ => rfl
  have hkQ : RingHom.ker augQ ^ (M + 1 + 1) = ⊥ := by
    have hle : RingHom.ker augQ ≤ (RingHom.ker (Chart.jetAug k (Fin 1 × Fin d) (M + 1))).map π := by
      intro q hq
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact Ideal.mem_map_of_mem π hq
    rw [← le_bot_iff]
    refine (Ideal.pow_right_mono hle _).trans ?_
    rw [← Ideal.map_pow, Chart.ker_jetAug_pow, Ideal.map_bot]
  have hz : (Chart.spMap π ≫ y (M + 1)) ≫ f = toUnit _ ≫ η[G] := by
    have e : π.comp ψ₁ = (Algebra.ofId k _).comp (Chart.jetAug k (Fin d) (M + 1)) := by
      refine Chart.jet_ext fun j => ?_
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Chart.jetAug_zR, map_zero, hψ₁]
      exact Ideal.Quotient.eq_zero_iff_mem.2
        (Ideal.mem_map_of_mem (toJetHom k (Fin 1 × Fin d) (M + 1)) (Ideal.subset_span ⟨j, rfl⟩))
    have hy₁' : y (M + 1) ≫ f = Chart.spMap ψ₁ ≫ x (M + 1) := hy₁
    rw [Category.assoc, hy₁', ← Category.assoc, Chart.spMap_comp, e, ← Chart.spMap_comp, Category.assoc, hxa,
      ← Hom.one_def]
    exact MonObj.comp_one _
  have hzone : Chart.spMap augQ ≫ Chart.spMap π ≫ y (M + 1) = 1 := by
    rw [← Category.assoc, Chart.spMap_comp, haπ, hya]
  obtain ⟨a, ha, hza⟩ := hU _ augQ (M + 1) hkQ (pullback.lift _ (toUnit _) hz) (hext _ _ (by
    rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hzone]))
  have hM' : RingHom.ker aug ^ (M + 1 + 1) = ⊥ := by
    rw [pow_succ (RingHom.ker aug) (M + 1), hM, Ideal.bot_mul]
  obtain ⟨ψ, ⟨hψa, hψ⟩, -⟩ := hx.2.2 A aug (M + 1) hM' (io ≫ pullback.fst f η[G]) (by
    rw [← Category.assoc, hio, pullback.lift_fst])
  have hz0 : ∀ j, ψ₀ (Chart.zR (M + 1) j) = Chart.zR (M + 1) (0, j) := fun j =>
    (hψ₀ j).trans (toJet_X (M + 1) _)
  have heq : a.comp ψ = π.comp ψ₀ := by
    refine (hx.2.2 _ augQ (M + 1) hkQ (Chart.spMap π ≫ y (M + 1)) hzone).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · rw [← AlgHom.comp_assoc, ha, hψa]
    · rw [← Chart.spMap_comp, Category.assoc, ← hψ, ← Category.assoc, ← hza, pullback.lift_fst]
    · rw [← AlgHom.comp_assoc, haπ]
      refine Chart.jet_ext fun j => ?_
      rw [AlgHom.comp_apply, hz0, Chart.jetAug_zR, Chart.jetAug_zR]
    · rw [hy₀, ← Category.assoc, Chart.spMap_comp]
  let Θ := π.comp (toJetHom k (Fin 1 × Fin d) (M + 1))
  have hΘ : Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS k 1 d)) ≤
      ((RingHom.ker aug).map a).comap Θ := by
    rw [Ideal.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have e1 : Θ (MvPowerSeries.X (0, j)) = a (ψ (Chart.zR (M + 1) j)) := by
      have := AlgHom.congr_fun heq (Chart.zR (M + 1) j)
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hψ₀] at this
      exact this.symm
    show Θ (MvPowerSeries.X (0, j)) ∈ (RingHom.ker aug).map a
    rw [e1]
    exact Ideal.mem_map_of_mem a ((AlgHom.congr_fun hψa _).trans (Chart.jetAug_zR (M + 1) j))
  intro g hg
  have h2 := Ideal.le_comap_pow _ (M + 1) (Ideal.pow_right_mono hΘ (M + 1) hg)
  rw [← Ideal.map_pow, hM, Ideal.map_bot] at h2
  exact mem_sup_pow_of_toJet_mem_map (M + 1) _ g (Ideal.Quotient.eq_zero_iff_mem.1 h2)

end GlobalTheory.JetSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGPassesToPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory.PrimDown

theorem exists_down_id {X₀ X' Y : Scheme.{0}} {L : LB X₀} {L' : LB X'} {F : X' ⟶ X₀} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (y : Y) p q, y ∈ LB.wchart L (fun k => φ' k ≫ F) p → y ∈ LB.wchart L' φ' q →
        gm (𝟙 Y) y _ (a.s q) = (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (y : Y) p,
      y ∈ LB.wchart L (fun k => φ' k ≫ F) p → y ∈ LB.wchart L' φ' q →
      gm (𝟙 Y) y _ s = (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q
    have hv : ∀ (y : Y) p, y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm (𝟙 Y) y _ ((u p q)⁻¹ * res inf_le_left (t.s p)) =
          (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) :=
      fun y p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹) (hu p q _ _ y hz)))
        (gm_res _ y _ hz _))
    obtain ⟨s, hs⟩ := glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q) (fun _ => inf_le_right)
      (fun y hy => by
        choose p hp using fun k => exists_chart hL (F (φ' k y))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))
      (fun p p' y hy => by
        rw [hv y p hy.1, hv y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          trF_self hL' _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun y p h₁ h₂ => ?_⟩
    have hz : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res _ y inf_le_right hz s).symm.trans ((congrArg (gm _ y _) (hs p)).trans (hv y p hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun y p q h₁ h₂ => hs q y p h₁ h₂⟩
  choose p hp using fun k => exists_chart hL (F (φ' k y))
  have m : y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
  refine (hs j y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' y p m hj')).symm)
  rw [pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv, _root_.mul_assoc]

theorem exists_down_all {X₀ X' Y : Scheme.{0}} {L : LB X₀} {L' : LB X'} {F : X' ⟶ X₀} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
          gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
            pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
  obtain ⟨a, ha, hv⟩ := exists_down_id hw hL hL' t ht
  obtain ⟨t₁, -, hu⟩ := exists_up hw hL hL' a ha
  have e : ∀ p, t.s p = t₁.s p := fun p => unit_ext fun y hy => by
    choose q hq using fun k => exists_chart hL' (φ' k y)
    have m : y ∈ LB.wchart L' φ' q := Set.mem_iInter.2 hq
    refine Eq.trans ?_ (hu _ (𝟙 Y) y p q hy m).symm
    exact (mul_inv_cancel_left _ _).symm.trans (congrArg _ (hv y p q hy m).symm)
  exact ⟨a, ha, fun Z r z p q hp hq => (congrArg (gm r z _) (e p)).trans (hu Z r z p q hp hq)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem prod_eSec {X0 : Scheme.{0}} (t : SAB H X0) {U : Type} [CommGroup U]
    (h : ((𝟙_ (Over X0)).left ⟶ t.G.left) → U) :
    ∏ k, h (eSec t.G ≫ primφ t k) ^ primε k = h (eSec t.G) := by
  have hpt : ∀ I : ULift.{0} (Finset (Fin 2)), eSec t.G ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
      (psum t.G ![1, η[t.G] ≫ t.act.act H.w0] I.down).left := by
    intro I
    simp only [cφG, eSec, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · exact (Category.comp_id _).trans (GermB.eta_one t.G)
    · rfl
  rw [Fintype.prod_sum_type]
  simp only [primφ, primε, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, zpow_neg,
    Finset.prod_inv_distrib, zpow_one]
  have z := (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) (hpt I)).trans
    (GermB.cube_one_left t (fun p => h p.left) (η[t.G] ≫ t.act.act H.w0))
  exact (congrArg (fun u => h (eSec t.G) * u⁻¹) z).trans (by rw [inv_one, _root_.mul_one])

end GlobalTheory.PrimDown

namespace GlobalTheory

theorem primG_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 X1 : Scheme.{0}) (t : SAB H X0) (t' : SAB H X1) (f : X1 ⟶ X0) (mp : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ wP : PrimTyG t, IsPrimG t wP → ∃ wP' : PrimTyG t', IsPrimG t' wP' ∧ (∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun k => primφ t' k ≫ mp.φ) primε), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (LB.pullGen t.PP.L _ _ wP mp.φ) ∧ LB.Gen.Maps (LB.linCombIso w (primφ t') primε) wP' (flatGen t.PP.L mp.φ _ _ c₁)) := by
  intro E _ _ _ H X0 X1 t t' f mp w hw wP hP
  have hL := t.PP.isLB
  have hL' := t'.PP.isLB
  obtain ⟨c₁, hc₁, hcc⟩ := ChartPrimTrPf.exists_reindex t.PP.L (φ := fun k => mp.φ ≫ primφ t k)
    (φ' := fun k => primφ t' k ≫ mp.φ) (funext fun k => ChartPrimTrPf.primφ_comm mp k) primε
    (LB.pullGen t.PP.L (primφ t) primε wP mp.φ) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hP.1 _)
  obtain ⟨a, ha, R⟩ := PrimDown.exists_down_all ((isGen_iff w).1 hw.1) hL hL' c₁ hc₁
  refine ⟨a, ⟨ha, corr_of_val hL' fun y J' hJ' => ?_⟩, c₁, hcc, ChartPrimTrPf.maps_flat w _ _ a c₁ R⟩
  choose J hJ using fun χ : (𝟙_ (Over X1)).left ⟶ t.G.left => exists_chart hL (χ y)
  have hJ : Good t.PP.L y J := hJ
  have pm := (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig mp.cm.e _
    (rigPull_le mp.cm.F mp.cm.e mp.cm.e_comm t.PP.L) (fun _ => rfl)).1 hw.2
  have e₁ := pm _ (𝟙 _) y (fun _ => J (eSec t'.G ≫ mp.φ)) (fun _ => J' (eSec t'.G)) (fun _ => hJ _) (fun _ => hJ' _)
  rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp] at e₁
  have e₂ : val c₁ (eSec t'.G) y J =
      gw w (eSec t'.G) y (J (eSec t'.G ≫ mp.φ)) (J' (eSec t'.G)) * val a (eSec t'.G) y J' := by
    refine (R _ (eSec t'.G) y _ _ (hJ.mem _ _) (hJ'.mem _ _)).trans (congrArg₂ (· * ·) ?_ rfl)
    refine Eq.trans ?_ (PrimDown.prod_eSec t' (fun q => gw w q y (J (q ≫ mp.φ)) (J' q)))
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Category.assoc]
  have e₃ : val c₁ (eSec t'.G) y J = val (L := t.PP.L) (φ := fun _ : PUnit => eSec t.G) (ε := fun _ => 1)
      t.PP.rig mp.cm.e y J := by
    refine (val_corr hJ hcc _).trans ((val_pull hJ _ _ _).trans ?_)
    refine Eq.trans ?_ (val_corr hJ hP.2 _)
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    exact congrArg (fun r => val (L := t.PP.L) (φ := primφ t) (ε := primε) wP r y J) mp.cm.e_comm
  have e₄ := (val_of (L := t.PP.L) (φ := fun _ : PUnit => eSec t.G) (ε := fun _ => 1) t.PP.rig mp.cm.e y J
    (fun _ => J (eSec t'.G ≫ mp.φ)) (fun _ => congrArg J mp.cm.e_comm.symm)).trans e₁
  have e₅ := mul_left_cancel (e₂.symm.trans (e₃.trans e₄))
  refine (val_pull hJ' _ _ _).trans ?_
  rw [Category.id_comp]
  refine e₅.trans ?_
  exact (val_of (L := t'.PP.L) (φ := fun _ : PUnit => eSec t'.G) (ε := fun _ => 1) t'.PP.rig (𝟙 _) y J' _
    (fun _ => by rw [Category.id_comp])).symm

end GlobalTheory
end
end

