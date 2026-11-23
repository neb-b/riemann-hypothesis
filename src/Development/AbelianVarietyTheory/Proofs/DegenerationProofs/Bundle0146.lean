module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsOfDouble
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AppellHumbertDataOfIsoCube

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelIsoOfValuedAgreementOverField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.FitMatch
open GlobalTheory.ArcPull GlobalTheory.ArcDataDescent

section General
variable {F F' : Type} [Field F] [Field F'] {B B₀ Y Y₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀}

theorem genRel_of_gauge {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen) {K : Type} [Fintype K] {pt : K → (Sp F ⟶ B)}
    {pt₀ : K → (Sp F ⟶ B₀)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb M pt ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)}
    (ht : t.IsGen) (ht₀ : t₀.IsGen) (x : Fˣ) (hp : ∀ k, pt k ≫ φ = pt₀ k) (z : Sp F) {J J'} (hJ : Good M₀ z J)
    (hJ' : Good M z J')
    (H : (∏ k, om w z J J' (pt k) ^ ε k) * val t (𝟙 _) z J' = Units.map (toStk z).toMonoidHom x * val t₀ (𝟙 _) z J) :
    GenRel w t t₀ (x : F) := by
  obtain rfl : (fun k => pt k ≫ φ) = pt₀ := funext hp
  refine (genRel_iff w t t₀ x z).2 ⟨hp, fun j j₀ h₀ h₁ => ?_⟩
  rw [val_of t _ z J' (fun k => J' (pt k)) (fun k => by rw [Category.id_comp]),
    val_of t₀ _ z J (fun k => J (pt k ≫ φ)) (fun k => by rw [Category.id_comp])] at H
  have m₀ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) j₀ := Set.mem_iInter.2 h₀
  have m₁ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt j := Set.mem_iInter.2 h₁
  have n₀ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) (fun k => J (pt k ≫ φ)) :=
    Set.mem_iInter.2 fun k => hJ (pt k ≫ φ)
  have n₁ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart M pt (fun k => J' (pt k)) :=
    Set.mem_iInter.2 fun k => hJ' (pt k)
  have a := pw_trans ((isGen_iff w).1 hw) pt ε (𝟙 _) z m₀ n₀ m₁ n₁
  simp only [pw, Category.id_comp] at a
  have key : (∏ k, Geo.Tor.gw w (pt k) z (j₀ k) (j k) ^ ε k) * gm (𝟙 _) z (LB.wchart M pt j) (t.s j) =
      Units.map (toStk z).toMonoidHom x * gm (𝟙 _) z (LB.wchart M₀ (fun k => pt k ≫ φ) j₀) (t₀.s j₀) := by
    rw [a, gen_trans ht (𝟙 _) z m₁ n₁, gen_trans ht₀ (𝟙 _) z m₀ n₀]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul H
    simp only [om, ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  exact congrArg Units.val key

theorem genRel_ext_iff (hM : M.IsLB) (hM₀ : M₀.IsLB) (w : LB.Iso M (M₀.pull φ)) {K : Type} [Fintype K]
    {pt : K → (Y ⟶ B)} {pt₀ : K → (Y₀ ⟶ B₀)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb M pt ε)}
    {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} (ht : t.IsGen) (ht₀ : t₀.IsGen) (σ : F →+* F') (r : Sp F ⟶ Y) (r₀ : Sp F ⟶ Y₀)
    {s : Sp F' ⟶ Y} {s₀ : Sp F' ⟶ Y₀} (h : s = spMap σ ≫ r) (h₀ : s₀ = spMap σ ≫ r₀) (x : F) :
    GenRel w (LB.pullGen _ _ _ t s) (LB.pullGen _ _ _ t₀ s₀) (σ x) ↔
      GenRel w (LB.pullGen _ _ _ t r) (LB.pullGen _ _ _ t₀ r₀) x := by
  subst h h₀
  refine Iff.trans ?_ (genRel_pull_iff σ w (LB.pullGen _ _ _ t r) (LB.pullGen _ _ _ t₀ r₀) x)
  have p : (fun k => (spMap σ ≫ r) ≫ pt k) = fun k => spMap σ ≫ r ≫ pt k := funext fun _ => Category.assoc _ _ _
  have p₀ : (fun k => (spMap σ ≫ r₀) ≫ pt₀ k) = fun k => spMap σ ≫ r₀ ≫ pt₀ k := funext fun _ => Category.assoc _ _ _
  refine genRel_congr hM hM₀ w p p₀ (t := LB.pullGen _ _ _ t (spMap σ ≫ r))
    (t' := LB.pullGen _ _ _ (LB.pullGen _ _ _ t r) (spMap σ)) (t₀ := LB.pullGen _ _ _ t₀ (spMap σ ≫ r₀))
    (t₀' := LB.pullGen _ _ _ (LB.pullGen _ _ _ t₀ r₀) (spMap σ))
    (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) _)
    (DVR.pullGen_isGen _ _ _ _ ht₀ _) (DVR.pullGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht₀ _) _)
    (fun y J hJ => ?_) (fun y J hJ => ?_) _ <;>
  rw [val_pull hJ, val_pull hJ, val_pull hJ, Category.assoc]

theorem toStk_vF {K : Type} [Fintype K] {pt : K → (Y ⟶ B)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M pt ε)) (r : Sp F ⟶ Y)
    {z : Sp F} {J} (hJ : Good M z J) : toStk z (vF t r J) = (val t r z J).val :=
  toStk_valF r _ z (hJ.mem pt r) _
end General

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {D : DegPre R} {D' : DegPre R'}
  {f : R →+* R'} {C : Type} [Field C] [Algebra (FractionRing R) C] [Algebra (FractionRing R') C]

theorem tf_comp (hf : Along f C) : (TF (R := R') C).hom ≫ spMap f = (TF (R := R) C).hom :=
  (congrArg (· ≫ spMap f) (Geo.Tor.spMap_comp _ _).symm).trans ((Geo.Tor.spMap_comp _ _).symm.trans
    ((congrArg spMap (RingHom.ext fun x => hf x)).trans (Geo.Tor.spMap_comp _ _)))

theorem c_of_field (hf : Along f C) {ψ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap f) ψ)
    (x : D'.X) (y : D.X) (h : (DegPre.cF D' C x).left ≫ ψ = (DegPre.cF D C y).left) :
    (D'.c x).left ≫ ψ = spMap f ≫ (D.c y).left := by
  have := D.P.isAb.proper
  let g : R' →+* C := (algebraMap (FractionRing R') C).comp (algebraMap R' _)
  have hg : Function.Injective g := (algebraMap (FractionRing R') C).injective.comp (IsFractionRing.injective _ _)
  have e : spMap g = (TF (R := R') C).hom := Geo.Tor.spMap_comp _ _
  refine ext_of_injective hg (X := Sp R') (π := spMap g) (p := 𝟙 _) (p' := 𝟙 _) (IsPullback.of_vert_isIso ⟨by simp⟩)
    D.P.A.hom ?_ ?_
  · rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w, Category.assoc]
    exact (Category.id_comp _).trans ((Category.comp_id _).symm.trans (congrArg _ (Over.w (D.c y)).symm))
  · rw [e, ← Category.assoc _ (spMap f), tf_comp hf, ← Category.assoc]
    exact h

theorem genRel_field (hf : Along f C) {N N' : NumD C} (ν : NumOf D C N) (ν' : NumOf D' C N')
    {ψ : D'.P.A.left ⟶ D.P.A.left} (he : eSec D'.P.A ≫ ψ = spMap f ≫ eSec D.P.A) {w : LB.Iso D'.P.L (D.P.L.pull ψ)}
    (hw : w.IsGen) (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf ψ (spMap f) he D.P.L D.rig)) (x : N'.X) (y : N.X) (h s : Cˣ)
    (hc : (DegPre.cF D' C (ν'.eX x)).left ≫ ψ = (DegPre.cF D C (ν.eX y)).left)
    (hψ : N'.ψ x * h = N.ψ y * s) (hh : (h : C) * wVal ν' ν w (N'.c x) = wVal ν' ν w 1) :
    GenRel w (LB.pullGen _ _ _ (D'.psi (ν'.eX x)) (jFK (R := R') C)) (LB.pullGen _ _ _ (D.psi (ν.eX y)) (jFK (R := R) C))
      (s : C) := by
  have z : Sp C := (default : PrimeSpectrum C)
  have hJ : Good D.P.L z ν.J := fun p => (top_le_iff_mem _ _ z).1 (ν.good p)
  have hJ' : Good D'.P.L z ν'.J := fun p => (top_le_iff_mem _ _ z).1 (ν'.good p)
  have hv : ∀ a, toStk z (wVal ν' ν w a) = (om w z ν.J ν'.J (ν'.eA a).left).val := fun a =>
    toStk_valF _ ((D.P.L.pull ψ).U (fun _ => ν.J ((ν'.eA a).left ≫ ψ)) ⊓ D'.P.L.U (ν'.J (ν'.eA a).left)) z
      ⟨mem_pull.2 (hJ ((ν'.eA a).left ≫ ψ)), hJ' _⟩ _
  have c₀ : ∀ a, (DegPre.cF D C a).left = jFK (R := R) C ≫ D.xK a := fun a => Category.assoc _ _ _
  have c₁ : ∀ a, (DegPre.cF D' C a).left = jFK (R := R') C ≫ D'.xK a := fun a => Category.assoc _ _ _
  have pm := (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (spMap f) _
    (rigPull_le ψ (spMap f) he D.P.L) (fun _ => rfl)).1 hr
  have e := pmaps_om (fun _ => he) pm (TF (R := R') C).hom z hJ hJ'
  rw [Fintype.prod_unique, zpow_one] at e
  replace e := (congrArg (fun q => val D.rig q z ν.J) (tf_comp hf).symm).trans e
  have a₀ := (congrArg (toStk z) (ν.ψ_eq y)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (toStk_vF _ _ hJ) ((toStk_vF _ _ hJ).trans (congrArg Units.val e))))
  have a₁ := (congrArg (toStk z) (ν'.ψ_eq x)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (toStk_vF _ _ hJ') (toStk_vF _ _ hJ')))
  have a₂ := congrArg (toStk z) hh
  rw [map_mul, hv, hv, ν'.c_eq, c₁, map_one] at a₂
  let U := Units.map (toStk z).toMonoidHom
  have b₀ : U (N.ψ y) = _ * (_ * _) := Units.ext a₀
  have b₁ : U (N'.ψ x) = _ * _ := Units.ext a₁
  have b₂ : U h * _ = om w z ν.J ν'.J ((TF (R := R') C).hom ≫ eSec D'.P.A) := Units.ext a₂
  have b₃ := congrArg U hψ
  rw [map_mul, map_mul, b₀, b₁, ← b₂] at b₃
  refine genRel_of_gauge hw (DVR.pullGen_isGen _ _ _ _ (D'.psi_gen _) _) (DVR.pullGen_isGen _ _ _ _ (D.psi_gen _) _) s
    (fun _ => (congrArg (· ≫ ψ) (c₁ _).symm).trans (hc.trans (c₀ _))) z hJ hJ' ?_
  rw [Fintype.prod_unique, val_pull hJ, val_pull hJ', Category.id_comp, Category.id_comp, zpow_neg_one]
  have e' := congrArg Additive.ofMul b₃
  apply Additive.ofMul.injective
  simp only [U, ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

theorem match_of_fit : GlobalTheory.UT.LL → AllS fun {_} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {C} _ _ A u _ {_} M f {_} ν' J => ∀ u₀ : M.W, (u : C) = algebraMap (FractionRing M.W) C (algebraMap _ _ u₀) → ∀ ψ (he : eSec M.P.D.toPre.P.A ≫ ψ = spMap f ≫ eSec a.D₀.P.A) w e, Fit A u M f ν' J ψ w e → LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec M.P.D.toPre.P.A) (fun _ => 1)) M.P.D.toPre.rig (rigPullOf ψ (spMap f) he a.D₀.P.L a.D₀.rig) → (letI := H.starRing; ∀ x, (M.P.oD.onB.act x).left ≫ ψ = ψ ≫ (a.oa.onB.act x).left) → GlobalTheory.LN.Match a f u₀ M.P.D.toPre M.P.oD ψ he w e := by
  intro _ E _ _ _ H D l c O _ β O' _ _ _ b a C _ _ _ _ _ _ A u r o M f N' ν' J _ hf u₀ hu ψ he w e
    ⟨gp, hw, hp, hx, _, hh⟩ hr ha
  have hc : ∀ χ : A.N.X, (DegPre.cF M.P.D.toPre C (ν'.eX (J.e χ))).left ≫ ψ = (DegPre.cF a.D₀ C (A.ν.eX χ)).left :=
    fun χ => by
      rw [← ν'.c_eq, ← A.ν.c_eq]
      exact (congrArg (fun q => (ν'.eA q).left ≫ ψ) (J.c_eq χ)).trans (hp _)
  have inj : Function.Injective f := fun x y h => IsFractionRing.injective O' (FractionRing O')
    ((algebraMap (FractionRing O') C).injective ((hf x).symm.trans (by rw [h]; exact hf y)))
  refine ⟨gp, hw, hr, ha, fun y => ?_, fun F _ _ _ _ uF hF huF y => ?_⟩
  · obtain ⟨χ, rfl⟩ := A.ν.eX.surjective y
    rw [hx]
    exact c_of_field hf gp _ _ (hc χ)
  · obtain ⟨χ, rfl⟩ := A.ν.eX.surjective y
    have k := genRel_field hf A.ν ν' he hw hr (J.e χ) χ (J.h (A.N.c χ)) (u ^ (A.be.be χ χ / 2)) (hc χ) (J.ψ_eq χ)
      ((congrArg (fun q => (J.h (A.N.c χ) : C) * wVal ν' A.ν w q) (J.c_eq χ)).trans (hh _))
    have lift : ∀ (L : Type) [Field L] [Algebra (FractionRing M.W) L] [Algebra (FractionRing O') L], Along f L →
        jFK (R := O') L = spMap (algebraMap (FractionRing M.W) L) ≫ genMap inj := fun L _ _ _ h =>
      (congrArg spMap (IsLocalization.ringHom_ext (nonZeroDivisors O') (RingHom.ext fun x =>
        (h x).symm.trans (congrArg (algebraMap (FractionRing M.W) L) (fracMap_algebraMap inj x).symm)))).trans
        (Geo.Tor.spMap_comp _ _)
    have t := fun (L : Type) [Field L] [Algebra (FractionRing M.W) L] [Algebra (FractionRing O') L] (h : Along f L) =>
      genRel_ext_iff M.P.D.toPre.P.isLB a.D₀.P.isLB w (M.P.D.toPre.psi_gen (ν'.eX (J.e χ))) (a.D₀.psi_gen (A.ν.eX χ))
        (algebraMap (FractionRing M.W) L) (𝟙 _) (genMap inj) (s := jFK (R := M.W) L) (Category.comp_id _).symm (lift L h)
        (algebraMap M.W _ u₀ ^ (A.be.be χ χ / 2))
    rw [Units.val_zpow_eq_zpow_val, hu, ← map_zpow₀] at k
    have k' := (t F fun x => (hF x).symm).2 ((t C hf).1 k)
    rw [hx, huF, ← A.be_eq, ← map_zpow₀]
    exact k'

end GlobalTheory.FitMatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyPullbackGeneric
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericIso

theorem isDominant_of_flat {X Y : Scheme.{0}} [IsIntegral Y] (f : X ⟶ Y) [Flat f] [Nonempty X] : IsDominant f := by
  have h : genericPoint Y ∈ Set.range f :=
    (Flat.generalizingMap f).stableUnderGeneralization_range (genericPoint_specializes (f (Classical.arbitrary X)))
      ⟨_, rfl⟩
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← (genericPoint_spec Y).def]
  exact closure_mono (Set.singleton_subset_iff.2 h)

theorem nonempty_pullback_generic {R : Type} [CommRing R] [IsDomain R] {T X : Scheme.{0}} (g : T ⟶ X)
    (p : X ⟶ Spec (CommRingCat.of R)) [Flat g] [Flat p] (t : T) :
    Nonempty ↥(pullback g (pullback.fst p (jK R))) := by
  let ξ : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  have hs : jK R ξ ⤳ (g ≫ p) t := (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => by
    have h₁ : algebraMap R (FractionRing R) a ∈ IsLocalRing.maximalIdeal (FractionRing R) := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h₁
    obtain rfl : a = 0 := IsFractionRing.injective R (FractionRing R) (h₁.trans (map_zero _).symm)
    exact Ideal.zero_mem _
  obtain ⟨b, hb⟩ := (Flat.generalizingMap (g ≫ p)).stableUnderGeneralization_range hs ⟨t, rfl⟩
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := jK R) (g b) ξ hb
  obtain ⟨z, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := pullback.fst p (jK R)) b y hy.symm
  exact ⟨z⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {U : Unif I D A G} {U' : Unif I D' A' G'}
  {hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre} {j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G}
  {Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G}
  {w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))}

theorem GenericRel.point (hL : Laws) (hR : AdmBase R I) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hE : Enough U.toUnifPre U'.toUnifPre hD j) (hw : GenericRel U.toUnifPre U'.toUnifPre hD j Φ w)
    {B : Type} [CommRing B] [Algebra R B] {g' : Spec (CommRingCat.of B) ⟶ G'.left}
    {g : Spec (CommRingCat.of B) ⟶ G.left} {jL : U.LG.L.ι} {jL' : U'.LG.L.ι}
    (hB : IsAdicComplete (I.map (algebraMap R B)) B)
    (h₁ : g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (h₂ : g ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (h₃ : ⊤ ≤ g' ⁻¹ᵁ U'.LG.L.U jL') (h₄ : ⊤ ≤ g ⁻¹ᵁ U.LG.L.U jL)
    (h₅ : ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left),
      r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).hom.left ≫ (fstG I e G).left = ρ ≫ g)
    {Z : Scheme.{0}} (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left)
    (hr : r ≫ pullback.fst G'.hom (jK R) = ρ ≫ g') : r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R) = ρ ≫ g := by
  have c : (ρ ≫ g) ≫ G.hom = (r ≫ pullback.snd G'.hom (jK R)) ≫ jK R := by
    rw [Category.assoc, h₂, ← h₁, ← Category.assoc, ← hr, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨f₂, e₁, e₂⟩ : ∃ f₂ : Z ⟶ ((Over.pullback (jK R)).obj G).left, f₂ ≫ pullback.fst G.hom (jK R) = ρ ≫ g ∧
      f₂ ≫ pullback.snd G.hom (jK R) = r ≫ pullback.snd G'.hom (jK R) :=
    ⟨pullback.lift _ _ c, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  rw [← e₁, ← Category.assoc]
  refine congrArg (· ≫ _) (GlobalTheory.hom_ext_of_integral_ratios hL R I D A G U
    (fun k σ => ∃ σ', AgreeAll U.toUnifPre U'.toUnifPre hD j k σ σ') (fun k hk σ₀ => ?_) Z _ _ ?_ fun z => ?_)
  · obtain ⟨c, σ', σ, h⟩ := (hE k hk).1 σ₀
    exact ⟨c, σ, h.1, h.2.1, σ', h.2.2⟩
  · rw [e₂, Category.assoc]
    exact congrArg (r ≫ ·) (Over.w Φ.hom)
  · obtain ⟨i, hi⟩ := exists_chart U.LG.isLB ((r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R)) z)
    have hi' : (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' := by rw [hr]; exact h₃ (Set.mem_univ (ρ z))
    rw [Category.assoc, e₁]
    refine ⟨i, jL, hi, h₄ (Set.mem_univ (ρ z)), ?_⟩
    rintro k hk σ τ ⟨σ', hσ⟩ ⟨τ', hτ⟩
    have x := GlobalTheory.GenericIso.cross_identity R I hR D D' A A' G G' hG hG' U U' hD j B g' g jL jL' hB h₁ h₃ h₄ h₅ k σ τ σ' τ' hσ hτ Z ρ z
    rw [hw.2 k hk σ' σ hσ Z r z i jL' hi hi', hw.2 k hk τ' τ hτ Z r z i jL' hi hi', hr, _root_.mul_assoc,
      _root_.mul_assoc]
    exact congrArg _ ((mul_comm _ _).trans (x.symm.trans (mul_comm _ _)))

theorem GenericRel.comm (hL : Laws) (hR : AdmBase R I) (hI : I ≠ ⊤) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hj : LevelIso U.toUnifPre U'.toUnifPre hD j)
    (hE : Enough U.toUnifPre U'.toUnifPre hD j) (hw : GenericRel U.toUnifPre U'.toUnifPre hD j Φ w)
    (a' : G' ⟶ G') (a : G ⟶ G) (ha : ∀ e, (Over.pullback (thick R I e)).map a' ≫ (j e).hom =
      (j e).hom ≫ (Over.pullback (thick R I e)).map a) :
    (Over.pullback (jK R)).map a' ≫ Φ.hom = Φ.hom ≫ (Over.pullback (jK R)).map a := by
  have := hR.1
  have := U'.smooth
  have := U.separated
  have P : ∀ {S : Scheme.{0}} (t : S ⟶ Spec (CommRingCat.of R)) {X Y : Over (Spec (CommRingCat.of R))} (c : X ⟶ Y),
      ((Over.pullback t).map c).left ≫ pullback.fst Y.hom t =
        pullback.fst X.hom t ≫ c.left := fun e _ _ c => pullback.lift_fst _ _ _
  have : Nontrivial (R ⧸ I ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 (by rwa [zero_add, pow_one])
  let x : (thickObj R I 0 G').left := eSec (thickObj R I 0 G') (Classical.arbitrary (PrimeSpectrum (R ⧸ I ^ (0 + 1))))
  obtain ⟨i₁, m₁⟩ := exists_chart U.LG.isLB ((fstG I 0 G).left ((j 0).hom.left x))
  obtain ⟨i₂, m₂⟩ := exists_chart U.LG.isLB (a.left ((fstG I 0 G).left ((j 0).hom.left x)))
  obtain ⟨i₁', m₁'⟩ := exists_chart U'.LG.isLB ((fstG I 0 G').left x)
  obtain ⟨i₂', m₂'⟩ := exists_chart U'.LG.isLB (a'.left ((fstG I 0 G').left x))
  obtain ⟨B, _, _, g', g, hB, -, hf, ⟨b, -⟩, h₁, h₂, h₃, h₄, h₅⟩ := CompletedPoint.exists_completed_point I G G'
    (fun e => (j e).hom) (fun e => (hj e).2.1) x (U.LG.L.U i₁ ⊓ a.left ⁻¹ᵁ U.LG.L.U i₂)
    (U'.LG.L.U i₁' ⊓ a'.left ⁻¹ᵁ U'.LG.L.U i₂') ⟨m₁, m₂⟩ ⟨m₁', m₂'⟩
  have h₆ : ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left),
      r ≫ (fstG I e G').left = ρ ≫ g' ≫ a'.left → r ≫ (j e).hom.left ≫ (fstG I e G).left = ρ ≫ g ≫ a.left := by
    intro e Z ρ r hr
    have hr' : r ≫ pullback.fst G'.hom (thick R I e) = ρ ≫ g' ≫ a'.left := hr
    have c : (ρ ≫ g') ≫ G'.hom = (r ≫ pullback.snd G'.hom (thick R I e)) ≫ thick R I e := by
      rw [Category.assoc _ (pullback.snd _ _), ← pullback.condition, ← Category.assoc r, hr']
      simp only [Category.assoc, Over.w]
    obtain ⟨r₀, e₁, e₂⟩ : ∃ r₀ : Z ⟶ (thickObj R I e G').left, r₀ ≫ pullback.fst G'.hom (thick R I e) = ρ ≫ g' ∧
        r₀ ≫ pullback.snd G'.hom (thick R I e) = r ≫ pullback.snd G'.hom (thick R I e) :=
      ⟨pullback.lift _ _ c, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    obtain rfl : r = r₀ ≫ ((Over.pullback (thick R I e)).map a').left := by
      refine pullback.hom_ext ?_ ?_
      · rw [hr', Category.assoc, P, ← Category.assoc r₀, e₁, Category.assoc]
      · rw [← e₂, Category.assoc]
        exact congrArg (r₀ ≫ ·) (Over.w ((Over.pullback (thick R I e)).map a')).symm
    have e₃ := congrArg (· ≫ a.left) (h₅ e Z ρ r₀ e₁)
    have e₄ := congrArg (fun q => r₀ ≫ q.left ≫ pullback.fst G.hom (thick R I e)) (ha e)
    simp only [Over.comp_left, Category.assoc, P] at e₃ e₄ ⊢
    exact e₄.trans e₃
  have := (unifPre_genericFibre_surjective_appTop_and_isIntegral hL.globalFns R I D' A' G' U'.toUnifPre).2
  have := nonempty_pullback_generic g' G'.hom b
  have := isDominant_of_flat (pullback.snd g' (pullback.fst G'.hom (jK R)))
  have p₁ := hw.point hL hR hG hG' hE hB h₁ h₂ (fun y hy => (h₃ hy).1) (fun y hy => (h₄ hy).1) h₅
    (pullback.fst g' (pullback.fst G'.hom (jK R))) (pullback.snd g' (pullback.fst G'.hom (jK R)))
    pullback.condition.symm
  have p₂ := hw.point hL hR hG hG' hE (g' := g' ≫ a'.left) (g := g ≫ a.left) hB
    (by rw [Category.assoc, Over.w, h₁]) (by rw [Category.assoc, Over.w, h₂]) (fun y hy => (h₃ hy).2)
    (fun y hy => (h₄ hy).2) h₆ (pullback.fst g' (pullback.fst G'.hom (jK R)))
    (pullback.snd g' (pullback.fst G'.hom (jK R)) ≫ ((Over.pullback (jK R)).map a').left)
    (by rw [Category.assoc, P, ← Category.assoc, ← pullback.condition, Category.assoc])
  refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := pullback G'.hom (jK R))
    (pullback.snd G.hom (jK R)) ((Over.w _).trans (Over.w _).symm)
    (pullback.snd g' (pullback.fst G'.hom (jK R))) (pullback.hom_ext ?_ ?_))
  · have e₃ := congrArg (· ≫ a.left) p₁
    simp only [Over.comp_left, Category.assoc, P] at e₃ p₂ ⊢
    exact p₂.trans e₃.symm
  · rw [Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) ((Over.w _).trans (Over.w _).symm)

theorem GenericRel.one (hL : Laws) (hR : AdmBase R I) (hI : I ≠ ⊤) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hj : LevelIso U.toUnifPre U'.toUnifPre hD j)
    (hE : Enough U.toUnifPre U'.toUnifPre hD j) (hw : GenericRel U.toUnifPre U'.toUnifPre hD j Φ w) :
    η[(Over.pullback (jK R)).obj G'] ≫ Φ.hom = η[(Over.pullback (jK R)).obj G] := by
  have h := hw.comm hL hR hI hG hG' hj hE 1 1 fun e => by
    have := (hj e).1
    rw [Functor.map_one, Functor.map_one, MonObj.comp_one, MonObj.one_comp]
  rw [Functor.map_one, Functor.map_one, MonObj.comp_one] at h
  have e := congrArg (η[(Over.pullback (jK R)).obj G'] ≫ ·) h
  simp only [← Category.assoc, MonObj.comp_one] at e
  simpa [Hom.one_def] using e

end GlobalTheory.GenericIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyUniformisationTraitInAbelianLocus
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

namespace GlobalTheory.AbelianTrait

theorem isProper_snd_of_mem_abLocus {S : Scheme.{0}} (G : Over S) [IsSeparated G.hom] [LocallyOfFiniteType G.hom]
    {K : Type} [Field K] (t : Sp K ⟶ S) (p : Sp K) (hp : t p ∈ abLocus G) : IsProper (pullback.snd G.hom t) := by
  let K' := AlgebraicClosure K
  let u : Sp K' ⟶ Sp K := spMap (algebraMap K K')
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have q : Sp K' := (default : PrimeSpectrum K')
  have e : (u ≫ t) q = t p := congrArg (fun z => t z) (Subsingleton.elim (u q) p)
  have h₁ := hp K' (u ≫ t) ⟨q, e⟩
  have P := (IsPullback.of_hasPullback (pullback.snd G.hom t) u).paste_horiz (IsPullback.of_hasPullback G.hom t)
  have h₃ : UniversallyClosed (pullback.snd (pullback.snd G.hom t) u) := by
    rw [← P.isoPullback_hom_snd]
    infer_instance
  have : Nonempty (Sp K') := ⟨q⟩
  have hu : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) u :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed (pullback.snd G.hom t) :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu h₃
  exact ⟨⟩

theorem nonempty_pelUnif_of_abLocus : GlobalTheory.LN.UDvrSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (χ : Sp W ⟶ S) (t' : SAB H (Sp W)) (_ : SABMap t' t χ), GlobalTheory.LN.PolAt t' (jK W) → Set.range χ ⊆ abLocus t.G → Nonempty (PELUnif (maximalIdeal W) t') := by
  intro hU E _ _ _ H S t W _ _ _ hW χ t' m hpol hr
  have hG := t'.semi
  have := hG.smooth
  have := hG.separated
  let r : Sp (W ⧸ maximalIdeal W) ⟶ Sp W := spMap (Ideal.Quotient.mk (maximalIdeal W))
  have p : Sp (W ⧸ maximalIdeal W) := (default : PrimeSpectrum (ResidueField W))
  have h₀ : r p ∈ abLocus t'.G := (abLocus_pullback abLocusOne t.semi m.cart.1 (r p)).1 (hr ⟨_, rfl⟩)
  have h₁ : IsProper (pullback.snd t'.G.hom r) := isProper_snd_of_mem_abLocus t'.G (K := ResidueField W) r p h₀
  have := hG.comm
  have := hG.geomConnected
  obtain ⟨P, -⟩ := hU E H W hW t' hpol
    ⟨_, ZJ.isGt_splitExtOfAbelian _ ⟨inferInstance, by
      change Smooth (pullback.snd t'.G.hom r)
      infer_instance, h₁, by
      change GeometricallyConnected (pullback.snd t'.G.hom r)
      infer_instance⟩⟩
  exact ⟨P⟩

end GlobalTheory.AbelianTrait
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ObjStOfTripleReframe
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch
noncomputable section
namespace GlobalTheory.Ex.Arch

theorem int_eq_of_exp_div_eq {m n : ℤ} (h : ∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) :
    m = n := by
  have hd : ∀ k : ℕ, 0 < k → (k : ℤ) ∣ m - n := fun k hk => by
    obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h k hk)
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    have hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    refine ⟨-j, ?_⟩
    have : ((m - n : ℤ) : ℂ) = ((k * -j : ℤ) : ℂ) := by
      push_cast
      apply mul_left_cancel₀ hp
      have h2 := congrArg (· * (k : ℂ)) hj
      simp only [add_mul, div_mul_cancel₀ _ hk'] at h2
      linear_combination -h2
    exact_mod_cast this
  refine sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hd ((m - n).natAbs + 1) (Nat.succ_pos _)) ?_)
  rw [Int.natAbs_natCast]
  exact Nat.lt_succ_self _

theorem objSt_of_triple_reframe : Laws → TripleSt → ReframeSt → ObjSt := by
  intro laws hT hR E _ _ _ H D La _ _ EF g ty P Hm₀ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  obtain ⟨Q, oa, L₀, u₀, hg, hiso, hdet, ht₁, ht₂, hker, hact, hW⟩ :=
    hT E H D La EF g ty P Hm₀ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  obtain ⟨u, Hm, χ, Ef, F, hAH, hE, hF⟩ := hR Q L₀ g u₀ hg ht₁ ht₂
  have hΛ : ∀ a, F (P a) ∈ u.Λ := fun a => (u.ker _).1 ((hF _).trans ((hker _).2 ⟨a, rfl⟩))
  have hsur : ∀ z ∈ u.Λ, ∃ a, z = F (P a) := fun z hz => by
    obtain ⟨w, rfl⟩ := F.surjective z
    obtain ⟨a, ha⟩ := (hker w).1 ((hF w).symm.trans ((u.ker _).2 hz))
    exact ⟨a, by rw [ha]⟩
  have hW' : ∀ (k : ℕ) a b (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • F (P a))) (u.ex ((k : ℂ)⁻¹ • F (P b))) (unitOn c) := fun k a b c hk hc => by
    rw [← map_smul F, ← map_smul F, hF, hF]
    exact hW k a b c hk hc
  have hEf : ∀ a b, Ef ⟨F (P a), hΛ a⟩ ⟨F (P b), hΛ b⟩ = EF a b := fun a b => int_eq_of_exp_div_eq fun k hk => by
    have w₁ := PeriodPoint.weilIs_of_isAH laws Q rfl u hAH Ef hE k ⟨F (P a), hΛ a⟩ ⟨F (P b), hΛ b⟩
      (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have w₂ := hW' k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    exact congrArg Units.val
      (PrimUnif.unitOn_inj' (CommutatorPairing.weilIs_unique laws.globalFns Q.isAb Q.isLB w₁ w₂))
  have hact' : ∀ (a : 𝓞 E) z, u.ex (F fun k => ty k (a : E) * z k) = u.ex (F z) ≫ oa.act a := fun a z => by
    rw [hF, hF, hact]
  let d : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    LinearMap.pi fun k => ty k (H.w0 : E) • LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) k
  let G : (Fin Q.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ) := F.toLinearMap ∘ₗ d ∘ₗ F.symm.toLinearMap
  have hG : ∀ z, G (F z) = F fun k => ty k (H.w0 : E) * z k := fun z => by
    change F (d (F.symm (F z))) = _
    rw [F.symm_apply_apply]
    rfl
  have hGP : ∀ a, G (F (P a)) = F (P (H.w0 • a)) := fun a => by
    rw [hG]
    congr 1
    funext k
    exact (h4 _ _ _).symm
  have hGΛ : ∀ l ∈ u.Λ, G l ∈ u.Λ := fun l hl => by
    obtain ⟨a, rfl⟩ := hsur l hl
    rw [hGP]
    exact hΛ _
  have hGex : ∀ z, u.ex (G z) = u.ex z ≫ oa.act H.w0 := fun z => by
    obtain ⟨w, rfl⟩ := F.surjective z
    rw [hG, hact']
  have hχ := (@GlobalTheory.SelfCube.appellHumbert_data_of_iso_cube GlobalTheory.valAt'_rules
    (GlobalTheory.holFamily_lift GlobalTheory.valAt'_rules) Q Q.isAb.comm u Hm χ Ef
    ⟨hAH.1, hAH.2.2.1, hE, hAH.2.2.2⟩ (oa.act H.w0) G hGΛ hGex hiso).2
  refine ⟨Q, oa, u, Hm, χ, F, hΛ, hiso, hdet, hAH, hsur, fun a b => ?_, fun a => ?_, hact', hW'⟩
  · rw [← hEf]
    exact (hE ⟨F (P a), hΛ a⟩ ⟨F (P b), hΛ b⟩).symm
  · rw [hχ, ← hEf]
    congr 2
    exact Subtype.ext (hGP a)

end GlobalTheory.Ex.Arch
end
end

