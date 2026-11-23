module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueOfBasis
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaReal

open CommPairing GlobalLift VVRank ThetaCoord

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem exists_symLift_one (hL : L.IsLB) {k : ℤ} {ν : LB.Gen (negLB A L k T)} (hν : ν.IsGen) :
    ∃ θ : ThetaGrp A L k T, SymLift A L k 1 1 θ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J → tval θ r z J = 1 := by
  have h1 : (LB.oneGen L (Y := (T ⊗ A).left)).IsGen := SymLiftOdd.isGen_of_gm fun y j j' _ _ => by
    rw [trF, Fintype.prod_empty, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (translPt A (1 : T ⟶ A)).left]) (ε' := ![k, -k])
    (fun U _ f => by
      rw [Fintype.prod_empty, Fin.prod_univ_two, ThetaAct.translPt_one]
      simp) (LB.oneGen L) h1
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval (⟨1, t, ht⟩ : ThetaGrp A L k T) r z J = 1 := fun Z r z J hJ => (hv Z r z J hJ).trans (val_one _)
  refine ⟨⟨1, t, ht⟩, symLift_of_tval hL rfl hν (fun T' π z J hJ p => ?_) (fun T' π z J hJ p => ?_), hv'⟩
  · exact Finset.prod_eq_one fun _ _ => hv' _ _ _ _ hJ
  · rw [hv' _ _ _ _ hJ, hv' _ _ _ _ hJ, MonObj.comp_one, inv_one, _root_.one_mul, _root_.one_mul, _root_.one_mul,
      mul_inv_cancel]

theorem isActOf_self (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB)
    {ν : LB.Gen (negLB A L 1 T)} (hν : ν.IsGen) {a : ℤ} {m q : ℕ} (hq : Odd q)
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -1])} (hα : α.IsGen)
    {th : LB.Sec (LPow A L 1 T)} {s : LB.Sec (LPow A L a T)}
    (hs : IsTwistPull A L (mulT A T m) (snd T A ^ m) (lift_snd _ _) a 1 α th s)
    {y : T ⟶ A} (hm : y ^ m = 1) (hy : y ^ q = 1) {θ : ThetaGrp A L a T} (H : SymLift A L a q y θ) :
    IsActOf A L a θ s s := by
  have := hA.comm
  obtain ⟨θ₁, h₁, v₁⟩ := exists_symLift_one hL hν
  obtain ⟨θ', h', v'⟩ := exists_symLift_mulPull hA hL (one_dvd q) hα hy (hm.symm ▸ h₁)
  have hc := SymLiftOdd.symLift_unique hG hA hL hq θ θ' H h'
  refine isTwistPull_of_sv A hL θ.isGen fun z J hJ => ?_
  have e : tval θ (𝟙 _) z J = tval θ' (𝟙 _) z J := val_corr hJ hc _
  have e₁ := sv_mulPull hs (fst T A) hJ (snd T A)
  have e₂ := sv_mulPull hs (fst T A) hJ ((fst T A ≫ y) * snd T A)
  have e₃ := v' _ (fst T A) z J hJ (snd T A)
  rw [v₁ _ _ _ _ hJ, _root_.mul_one] at e₃
  rw [mul_pow, ← MonObj.comp_pow, hm, MonObj.comp_one, _root_.one_mul] at e₂
  change _ = (tval θ (𝟙 _) z J).val * _
  rw [e, SymLiftOdd.id_eq_lift, ThetaCoord.lift_translT, H.pt_eq, e₃, e₁, e₂, Units.val_mul, _root_.mul_assoc,
    Units.inv_mul_cancel_left]

theorem act_act (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {k : ℤ} {q : ℕ} (hq : Odd q) {x y : T ⟶ A}
    (hy : y ^ q = 1) {θx θy θ : ThetaGrp A L k T} (Hx : SymLift A L k q x θx) (Hy : SymLift A L k q y θy)
    (H : SymLift A L k q (y * x) θ) {c : Γ(T.left, ⊤)ˣ} (hc : WeilIs A L k x y c)
    {s s' s'' t : LB.Sec (LPow A L k T)} (h₁ : IsActOf A L k θy s s') (h₂ : IsActOf A L k θx s' s'')
    (h₃ : IsActOf A L k θ s t) :
    (SecM.ofSec A s'' : SecM A L k T) = ((c ^ ((q + 1) / 2) : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) • SecM.ofSec A t := by
  refine ThetaAct.sv_ext hL fun z J hJ => ?_
  have e₁ := sv_act Hx.pt_eq h₂ (fst T A) hJ (snd T A)
  have e₂ := sv_act Hy.pt_eq h₁ (fst T A) hJ ((fst T A ≫ x) * snd T A)
  have e₃ := sv_act H.pt_eq h₃ (fst T A) hJ (snd T A)
  have e₄ := tval_mul hG hA hL hq hy Hx Hy H hc (fst T A) hJ (snd T A)
  rw [← _root_.mul_assoc, ← MonObj.comp_mul] at e₂
  rw [ThetaAct.sv_smul _ _ _ _ hJ, Category.id_comp, gs_unit _ _ ⊤ trivial, map_pow, SymLiftOdd.id_eq_lift]
  refine e₁.trans ?_
  rw [e₂, ← _root_.mul_assoc, ← Units.val_mul, e₄, Units.val_mul, _root_.mul_assoc, ← e₃]
  rfl

theorem sum_iff {k : ℤ} {κ : Type} [Fintype κ] (σ : LB.Sec (LPow A L k T)) (s : κ → SecM A L k T)
    (c : κ → Γ(T.left, ⊤)) :
    (∀ j, σ.f j = ∑ i, liftFun A _ (c i) * (SecM.toSec A (s i)).f j) ↔ SecM.ofSec A σ = ∑ i, c i • s i := by
  have e : ∀ j, (∑ i, c i • s i : SecM A L k T).1 j = ∑ i, liftFun A _ (c i) * (SecM.toSec A (s i)).f j := fun j => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  exact ⟨fun h => Subtype.ext (funext fun j => (h j).trans (e j).symm),
    fun h j => (congrArg (fun q => q.1 j) h).trans (e j)⟩

theorem existsUnique_of_basis {k : ℤ} {κ : Type} [Fintype κ] (s : Module.Basis κ Γ(T.left, ⊤) (SecM A L k T))
    (σ : LB.Sec (LPow A L k T)) :
    ∃! c : κ → Γ(T.left, ⊤), ∀ j, σ.f j = ∑ i, liftFun A _ (c i) * (SecM.toSec A (s i)).f j := by
  simp only [sum_iff]
  exact ⟨s.equivFun (SecM.ofSec A σ), (s.sum_equivFun _).symm, fun c hc => by
    rw [hc, ← s.equivFun_symm_apply, LinearEquiv.apply_symm_apply]⟩

theorem UnivBasis.exists_basis {P : PolAV S} [IsAffine T.left] {n : ℤ} {κ : Type} {b : κ → SecM P.A P.L n T}
    (h : UnivBasis P n b) : ∃ c : Module.Basis κ Γ(T.left, ⊤) (SecM P.A P.L n T), ∀ i, c i = b i := by
  obtain ⟨c, hc⟩ := h T (𝟙 T)
  exact ⟨c, fun i => (hc i).trans (pullM_id P.A P.isLB n _)⟩

theorem UnivBasis.unique {P : PolAV S} {n : ℤ} {κ : Type} [Unique κ] {b : κ → SecM P.A P.L n T}
    (h : UnivBasis P n b) : UnivBasis P n (fun _ : Fin 1 => b default) := fun T' _ u => by
  obtain ⟨c, hc⟩ := h T' u
  refine ⟨c.reindex (Equiv.ofUnique κ (Fin 1)), fun i => ?_⟩
  rw [Module.Basis.reindex_apply, hc, Subsingleton.elim ((Equiv.ofUnique κ (Fin 1)).symm i) default]

end GlobalTheory.ThetaReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourthSideRespectsRigSymmetryCube
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.FourthSide

section General
variable {S Z : Scheme.{0}} {G : Over S} [GrpObj G] {s s' : Z ⟶ S}

theorem mul_left_congr {x y : Over.mk s ⟶ G} {x' y' : Over.mk s' ⟶ G} (hx : x.left = x'.left)
    (hy : y.left = y'.left) : (x * y).left = (x' * y').left := by
  obtain rfl : s = s' := (Over.w x).symm.trans ((congrArg (· ≫ G.hom) hx).trans (Over.w x'))
  rw [Over.OverMorphism.ext hx, Over.OverMorphism.ext hy]

theorem cubV_congr [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) (z : Z) (J) {x y u : Over.mk s ⟶ G}
    {x' y' u' : Over.mk s' ⟶ G} (hx : x.left = x'.left) (hy : y.left = y'.left) (hu : u.left = u'.left) :
    @id (Z.presheaf.stalk z)ˣ (cubV c (T := Over.mk s) z J x y u) =
      @id (Z.presheaf.stalk z)ˣ (cubV c (T := Over.mk s') z J x' y' u') := by
  obtain rfl : s = s' := (Over.w x).symm.trans ((congrArg (· ≫ G.hom) hx).trans (Over.w x'))
  rw [Over.OverMorphism.ext hx, Over.OverMorphism.ext hy, Over.OverMorphism.ext hu]

end General

theorem cube_alg {A A₀ A₁ A₂ M : Type} [CommGroup A] [CommGroup A₀] [CommGroup A₁] [CommGroup A₂] [CommGroup M]
    (n : A →* A₀) (a : A →* A₁) (b : A →* A₂) {W : A → M} {W₀ : A₀ → M} {W₁ : A₁ → M} {W₂ : A₂ → M}
    (sq : ∀ x, W₂ (b x) * W x = W₀ (n x) * W₁ (a x)) (x y u : A) {C C' E E' : M}
    (h₀ : C * W₀ (n x * n y) * W₀ (n x * n u) * W₀ (n y * n u) * W₀ 1 =
      W₀ (n x * n y * n u) * W₀ (n x) * W₀ (n y) * W₀ (n u) * E)
    (h₁ : E * W₁ (a x * a y) * W₁ (a x * a u) * W₁ (a y * a u) * W₁ 1 =
      W₁ (a x * a y * a u) * W₁ (a x) * W₁ (a y) * W₁ (a u) * E')
    (h₂ : C * W₂ (b x * b y) * W₂ (b x * b u) * W₂ (b y * b u) * W₂ 1 =
      W₂ (b x * b y * b u) * W₂ (b x) * W₂ (b y) * W₂ (b u) * C') :
    C' * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * E' := by
  have e : ∀ x, W x = (W₂ (b x))⁻¹ * (W₀ (n x) * W₁ (a x)) := fun x => eq_inv_mul_of_mul_eq (sq x)
  simp only [e, map_mul, map_one]
  apply Additive.ofMul.injective
  have k₀ := congrArg Additive.ofMul h₀
  have k₁ := congrArg Additive.ofMul h₁
  have k₂ := congrArg Additive.ofMul h₂
  simp only [ofMul_mul, ofMul_inv] at k₀ k₁ k₂ ⊢
  linear_combination (norm := abel) k₀ + k₁ - k₂

theorem sym_alg {A A₀ A₁ A₂ M : Type} [CommGroup A] [CommGroup A₀] [CommGroup A₁] [CommGroup A₂] [CommGroup M]
    (n : A →* A₀) (a : A →* A₁) (b : A →* A₂) {W : A → M} {W₀ : A₀ → M} {W₁ : A₁ → M} {W₂ : A₂ → M}
    (sq : ∀ x, W₂ (b x) * W x = W₀ (n x) * W₁ (a x)) (x : A) {C C' E E' : M}
    (h₀ : C * W₀ (n x) = W₀ (n x)⁻¹ * E) (h₁ : E * W₁ (a x) = W₁ (a x)⁻¹ * E')
    (h₂ : C * W₂ (b x) = W₂ (b x)⁻¹ * C') : C' * W x = W x⁻¹ * E' := by
  have e : ∀ x, W x = (W₂ (b x))⁻¹ * (W₀ (n x) * W₁ (a x)) := fun x => eq_inv_mul_of_mul_eq (sq x)
  simp only [e, map_inv]
  apply Additive.ofMul.injective
  have k₀ := congrArg Additive.ofMul h₀
  have k₁ := congrArg Additive.ofMul h₁
  have k₂ := congrArg Additive.ofMul h₂
  simp only [ofMul_mul, ofMul_inv] at k₀ k₁ k₂ ⊢
  linear_combination (norm := abel) k₀ + k₁ - k₂

theorem rig_alg {M : Type} [CommGroup M] {W W₀ W₁ W₂ C C' E E' : M} (sq : W₂ * W = W₀ * W₁) (h₀ : C = W₀ * E)
    (h₁ : E = W₁ * E') (h₂ : C = W₂ * C') : C' = W * E' :=
  mul_left_cancel (a := W₂) (by rw [← h₂, h₀, h₁, ← _root_.mul_assoc, ← _root_.mul_assoc, sq])

theorem pG_mul {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {e : ℕ} (g : GtCoord I D e G)
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x y : T ⟶ thickObj R I e G) :
    toBase (A' := thickObj R I e G) (f := thick R I e) (g := g.pG.left) (Over.w g.pG) (x * y) =
      toBase (Over.w g.pG) x * toBase (Over.w g.pG) y := by
  have := g.q_hom
  have := toBase_mul_pullback D.P.A (thick R I e) T (x ≫ g.q) (y ≫ g.q)
  rw [← MonObj.mul_comp] at this
  have a : ∀ x : T ⟶ thickObj R I e G, toBase (Over.w g.pG) x =
      toBase (A := D.P.A) (g := pullback.fst D.P.A.hom (thick R I e)) pullback.condition (x ≫ g.q) :=
    fun x => Over.OverMorphism.ext (Category.assoc _ _ _).symm
  exact (a _).trans (this.trans (congrArg₂ (· * ·) (a x) (a y)).symm)


set_option maxHeartbeats 1000000 in
theorem fourth_side_vals : ∀ (hG : GlobalFnsSt) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (P' : CP G') (F : G'.left ⟶ G.left) (hF : F ≫ G.hom = G'.hom ≫ spMap φ) (wL : LB.Iso P'.L.L (U.P.L.L.pull F)), IsCPMap P' U.P (spMap φ) F hF wL → ∀ (β : D'.P.A.left ⟶ D.P.A.left) (hβ : β ≫ D.P.A.hom = D'.P.A.hom ≫ spMap φ) (v : LB.Iso D'.P.L (D.P.L.pull β)), IsCPMap (CP.ofDegPre hG D') (CP.ofDegPre hG D) (spMap φ) β hβ v → ∀ (e : ℕ) (g' : GtCoord I' D' e G') (h : (thickObj V I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ F → g'.pG.left ≫ β = h ≫ (U.gt e).pG.left → ∀ w' : LB.Iso (P'.L.L.pull (fstG I' e G').left) (D'.P.L.pull g'.pG.left), (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V I' e G').left) (z : Z) (jM : D.P.L.ι) (jM' : D'.P.L.ι) (jL : U.P.L.L.ι) (jL' : P'.L.L.ι), β (g'.pG.left (r z)) ∈ D.P.L.U jM → g'.pG.left (r z) ∈ D'.P.L.U jM' → F ((fstG I' e G').left (r z)) ∈ U.P.L.L.U jL → (fstG I' e G').left (r z) ∈ P'.L.L.U jL' → gw v (r ≫ g'.pG.left) z jM jM' * gw w' r z jM' (fun _ => jL') = gw (U.w e) (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ (fstG I' e G').left) z jL jL') → ∀ (T : Over (Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))))) (z : T.left) (JG : (T.left ⟶ G'.left) → P'.L.L.ι) (J : (T.left ⟶ D'.P.A.left) → D'.P.L.ι), Good P'.L.L z JG → Good D'.P.L z J → ∀ W : (T ⟶ thickObj V I' e G') → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w' x.left z (J (x.left ≫ g'.pG.left)) (fun _ => JG (x.left ≫ (fstG I' e G').left))) → (val (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (T.hom ≫ thick V I' e) z J = W 1 * val (L := P'.L.L) (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) P'.L.rig (T.hom ≫ thick V I' e) z JG) ∧ (∀ x : T ⟶ thickObj V I' e G', val D'.sym (x.left ≫ g'.pG.left) z J * W x = W x⁻¹ * val P'.sym (x.left ≫ (fstG I' e G').left) z JG) ∧ ∀ x y u : T ⟶ thickObj V I' e G', @id (T.left.presheaf.stalk z)ˣ (cubV D'.cub (T := (Over.map (thick V I' e)).obj T) z J ((Over.map (thick V I' e)).map x ≫ g'.pG) ((Over.map (thick V I' e)).map y ≫ g'.pG) ((Over.map (thick V I' e)).map u ≫ g'.pG)) * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * @id (T.left.presheaf.stalk z)ˣ (cubV P'.c (T := (Over.map (thick V I' e)).obj T) z JG ((Over.map (thick V I' e)).map x ≫ fstG I' e G') ((Over.map (thick V I' e)).map y ≫ fstG I' e G') ((Over.map (thick V I' e)).map u ≫ fstG I' e G')) := by
  intro hG R V _ _ _ _ I I' φ hle D D' A G _ _ G' _ _ U P' F hF wL hwL β hβ v hv e g' h hh hp w' hsq T z JG J hJG hJ W hW
  have hpow : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hle _
  obtain ⟨σ, hσ⟩ : ∃ σ : Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))),
      σ ≫ thick R I e = thick V I' e ≫ spMap φ :=
    ⟨spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hpow), by rw [← Spec.map_comp, ← Spec.map_comp]; rfl⟩
  have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have := Cmp.mono_fstG I e G
  have hb : (T.hom ≫ σ) ≫ thick R I e = (T.hom ≫ thick V I' e) ≫ spMap φ := by
    rw [Category.assoc, hσ, Category.assoc]
  let a := toBaseHom (toBase_mul_pullback G' (thick V I' e)) T
  let b := toBaseHom (pG_mul g') T
  have ha : ∀ x : T ⟶ thickObj V I' e G', (x.left ≫ h) ≫ (fstG I e G).left = (a x).left ≫ F := fun x =>
    (Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) hh).trans (Category.assoc _ _ _).symm)
  have hq : ∀ x : T ⟶ thickObj V I' e G', (x.left ≫ h) ≫ (U.gt e).pG.left = (b x).left ≫ β := fun x =>
    (Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) hp.symm).trans (Category.assoc _ _ _).symm)
  have hs : ∀ x : T ⟶ thickObj V I' e G', (x.left ≫ h) ≫ (thickObj R I e G).hom = T.hom ≫ σ := fun x => by
    rw [← cancel_mono (thick R I e), hb, Category.assoc]
    refine (congrArg ((x.left ≫ h) ≫ ·) (Over.w (fstG I e G)).symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) (ha x)).trans ?_)
    exact Over.w (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hF (a x))
  let n₀ : (T ⟶ thickObj V I' e G') → (Over.mk (T.hom ≫ σ) ⟶ thickObj R I e G) :=
    fun x => Over.homMk (x.left ≫ h) (hs x)
  let n : (T ⟶ thickObj V I' e G') →* (Over.mk (T.hom ≫ σ) ⟶ thickObj R I e G) := MonoidHom.mk' n₀ fun x y => by
    refine Over.OverMorphism.ext ((cancel_mono (fstG I e G).left).1 ((ha (x * y)).trans ?_))
    rw [map_mul]
    refine (congrArg (fun q => q.left) (hwL.mul _ (a x) (a y))).trans (Eq.trans ?_
      (congrArg (fun q => q.left) (toBase_mul_pullback G (thick R I e) _ (n₀ x) (n₀ y))).symm)
    exact mul_left_congr (ha x).symm (ha y).symm
  obtain ⟨K, hK⟩ := exists_good_pt U.P.L.isLB z
  obtain ⟨J₀, hJ₀⟩ := exists_good_pt D.P.isLB z
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : (Over.mk (T.hom ≫ σ) ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ, ∀ x, W₀ x =
    gw (U.w e) x.left z (J₀ (x.left ≫ (U.gt e).pG.left)) (fun _ => K (x.left ≫ (fstG I e G).left)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨W₁, hW₁⟩ : ∃ W₁ : (Over.mk (T.hom ≫ thick V I' e) ⟶ G') → (T.left.presheaf.stalk z)ˣ, ∀ x, W₁ x =
    gw wL x.left z (K (x.left ≫ F)) (JG x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨W₂, hW₂⟩ : ∃ W₂ : (Over.mk (T.hom ≫ thick V I' e) ⟶ D'.P.A) → (T.left.presheaf.stalk z)ˣ, ∀ x, W₂ x =
    gw v x.left z (J₀ (x.left ≫ β)) (J x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨p₁, p₂, p₃⟩ := U.w_vals e (Over.mk (T.hom ≫ σ)) z K J₀ hK hJ₀ W₀ hW₀
  obtain ⟨q₁, q₂, q₃⟩ := hwL.vals (Over.mk (T.hom ≫ thick V I' e)) z JG K hJG hK W₁ hW₁
  obtain ⟨r₁, r₂, r₃⟩ := hv.vals (Over.mk (T.hom ≫ thick V I' e)) z J J₀ hJ hJ₀ W₂ hW₂
  have sq : ∀ x, W₂ (b x) * W x = W₀ (n x) * W₁ (a x) := fun x => by
    have k := hsq _ x.left z _ _ _ _ (hJ₀ ((b x).left ≫ β)) (hJ (b x).left) (hK ((a x).left ≫ F)) (hJG (a x).left)
    have k₀ : W₀ (n x) = gw (U.w e) (x.left ≫ h) z (J₀ ((b x).left ≫ β)) (fun _ => K ((a x).left ≫ F)) := by
      rw [← ha, ← hq]
      exact hW₀ (n x)
    rw [k₀, hW, hW₁, hW₂]
    exact k
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · have k := sq 1
    rw [map_one, map_one, map_one] at k
    have p : val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
        ((T.hom ≫ σ) ≫ thick R I e) z J₀ = W₀ 1 * val (L := U.P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1)
          U.P.L.rig ((T.hom ≫ σ) ≫ thick R I e) z K := p₁
    rw [hb] at p
    exact rig_alg k p q₁ r₁
  · have p : val D.sym ((x.left ≫ h) ≫ (U.gt e).pG.left) z J₀ * W₀ (n x) =
        W₀ (n x)⁻¹ * val U.P.sym ((x.left ≫ h) ≫ (fstG I e G).left) z K := p₂ (n x)
    rw [ha, hq] at p
    have q : val U.P.sym ((x.left ≫ (fstG I' e G').left) ≫ F) z K * W₁ (a x) =
        W₁ (a x)⁻¹ * val P'.sym (x.left ≫ (fstG I' e G').left) z JG := q₂ (a x)
    have r : val D.sym ((x.left ≫ g'.pG.left) ≫ β) z J₀ * W₂ (b x) =
        W₂ (b x)⁻¹ * val D'.sym (x.left ≫ g'.pG.left) z J := r₂ (b x)
    exact sym_alg n a b sq x p q r
  · let C : (T.left.presheaf.stalk z)ˣ := cubV D.cub (T := Over.mk ((T.hom ≫ thick V I' e) ≫ spMap φ)) z J₀
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hβ (b x))
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hβ (b y))
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hβ (b u))
    let E : (T.left.presheaf.stalk z)ˣ := cubV U.P.c (T := Over.mk ((T.hom ≫ thick V I' e) ≫ spMap φ)) z K
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hF (a x))
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hF (a y))
      (toBase (T := Over.mk (T.hom ≫ thick V I' e)) hF (a u))
    let C' : (T.left.presheaf.stalk z)ˣ := cubV D'.cub (T := Over.mk (T.hom ≫ thick V I' e)) z J (b x) (b y) (b u)
    let E' : (T.left.presheaf.stalk z)ˣ := cubV P'.c (T := Over.mk (T.hom ≫ thick V I' e)) z JG (a x) (a y) (a u)
    let C₀ : (T.left.presheaf.stalk z)ˣ := cubV D.cub (T := (Over.map (thick R I e)).obj (Over.mk (T.hom ≫ σ))) z J₀
      ((Over.map (thick R I e)).map (n x) ≫ (U.gt e).pG) ((Over.map (thick R I e)).map (n y) ≫ (U.gt e).pG)
      ((Over.map (thick R I e)).map (n u) ≫ (U.gt e).pG)
    let E₀ : (T.left.presheaf.stalk z)ˣ := cubV U.P.c (T := (Over.map (thick R I e)).obj (Over.mk (T.hom ≫ σ))) z K
      ((Over.map (thick R I e)).map (n x) ≫ fstG I e G) ((Over.map (thick R I e)).map (n y) ≫ fstG I e G)
      ((Over.map (thick R I e)).map (n u) ≫ fstG I e G)
    have hC : C₀ = C := cubV_congr (s := (T.hom ≫ σ) ≫ thick R I e) (s' := (T.hom ≫ thick V I' e) ≫ spMap φ)
      D.cub z J₀ (hq x) (hq y) (hq u)
    have hE : E₀ = E := cubV_congr (s := (T.hom ≫ σ) ≫ thick R I e) (s' := (T.hom ≫ thick V I' e) ≫ spMap φ)
      U.P.c z K (ha x) (ha y) (ha u)
    have p : C₀ * W₀ (n x * n y) * W₀ (n x * n u) * W₀ (n y * n u) * W₀ 1 =
      W₀ (n x * n y * n u) * W₀ (n x) * W₀ (n y) * W₀ (n u) * E₀ := p₃ (n x) (n y) (n u)
    have q : E * W₁ (a x * a y) * W₁ (a x * a u) * W₁ (a y * a u) * W₁ 1 =
      W₁ (a x * a y * a u) * W₁ (a x) * W₁ (a y) * W₁ (a u) * E' := q₃ (a x) (a y) (a u)
    have r : C * W₂ (b x * b y) * W₂ (b x * b u) * W₂ (b y * b u) * W₂ 1 =
      W₂ (b x * b y * b u) * W₂ (b x) * W₂ (b y) * W₂ (b u) * C' := r₃ (b x) (b y) (b u)
    rw [hC, hE] at p
    have k := cube_alg n a b sq x y u p q r
    have hC' : C' = cubV D'.cub (T := (Over.map (thick V I' e)).obj T) z J
        ((Over.map (thick V I' e)).map x ≫ g'.pG) ((Over.map (thick V I' e)).map y ≫ g'.pG)
        ((Over.map (thick V I' e)).map u ≫ g'.pG) :=
      cubV_congr (s := T.hom ≫ thick V I' e) (s' := T.hom ≫ thick V I' e) D'.cub z J rfl rfl rfl
    have hE' : E' = cubV P'.c (T := (Over.map (thick V I' e)).obj T) z JG
        ((Over.map (thick V I' e)).map x ≫ fstG I' e G') ((Over.map (thick V I' e)).map y ≫ fstG I' e G')
        ((Over.map (thick V I' e)).map u ≫ fstG I' e G') :=
      cubV_congr (s := T.hom ≫ thick V I' e) (s' := T.hom ≫ thick V I' e) P'.c z JG rfl rfl rfl
    rw [hC', hE'] at k
    exact k

end GlobalTheory.LN.FourthSide
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCubicalBundleMapOfPulledBackDegeneration
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.DegPullPackage

theorem isCPMap_of_rig (hG : GlobalFnsSt) {S S' : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
    {f : S' ⟶ S} {B' : Over S'} [GrpObj B'] [IsCommMonObj B'] (hB' : IsAbelianScheme B') (M : CP B) (M' : CP B')
    {β : B'.left ⟶ B.left} {hw : β ≫ B.hom = B'.hom ≫ f}
    (mul : ∀ (T : Over S') (x y : T ⟶ B'), toBase hw (x * y) = toBase hw x * toBase hw y)
    (w : LB.Iso M'.L.L (M.L.L.pull β)) (hg : w.IsGen)
    (he : eSec B' ≫ β = f ≫ eSec B)
    (hr' : PMaps w (fun _ : PUnit => eSec B') (fun _ => eSec B) (fun _ => 1) M'.L.rig M.L.rig f) :
    IsCPMap M' M f β hw w := by
  obtain ⟨rig, hr, c, s, hs, h₂, h₃, H⟩ := exists_isCPMap M mul M'.L.L M'.L.isLB w hg
  let N : CP B' := ⟨⟨M'.L.L, rig, M'.L.isLB, hr⟩, c, s, hs, h₂, h₃⟩
  have es : ∀ (Z : Scheme.{0}) (r : Z ⟶ B'.left) (z : Z) (J), Good M'.L.L z J → val s r z J = val M'.sym r z J :=
    gen_unique M'.L.isLB B'.hom (1 : 𝟙_ (Over S') ⟶ B').left (Over.w _) (hG _ _ hB').2 hs M'.sym_gen
      fun y J hJ => (N.val_sym_one hJ).trans (M'.val_sym_one hJ).symm
  have ec : ∀ (T : Over S') (z : T.left) (J), Good M'.L.L z J → ∀ x y u : T ⟶ B',
      cubV c z J x y u = cubV M'.c z J x y u := fun T z J hJ x y u =>
    gen_unique M'.L.isLB (φ := thφ B' (x3 B')) (ε := thε) (G3 B').hom
      (lift (1 : 𝟙_ (Over S') ⟶ B') (lift 1 1)).left (Over.w _) (surjective_cube hG hB') c.isGen M'.c.isGen
      (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV M'.c hJ).face 1 1).symm) _ _ z J hJ
  refine ⟨mul, hg, fun T z J' J hJ' hJ W hW => ?_⟩
  obtain ⟨-, a₂, a₃⟩ := H.vals T z J' J hJ' hJ W hW
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · have e := CubTransport.val_pmaps (fun _ => he) hr' T.hom hJ hJ'
    rw [Fintype.prod_unique, zpow_one] at e
    rw [hW, one_left]
    exact e
  · exact (a₂ x).trans (congrArg (W x⁻¹ * ·) (es _ x.left z J' hJ'))
  · exact (a₃ x y u).trans (congrArg (W (x * y * u) * W x * W y * W u * ·) (ec T z J' hJ' x y u))

theorem isCPMap_of_isPullDeg : ∀ (hG : GlobalFnsSt) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (hD : IsPullDeg φ D D'), IsCPMap (CP.ofDegPre hG D') (CP.ofDegPre hG D) (spMap φ) (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (pull_grp hD).1.w hD.w := by
  intro hG R V _ _ _ _ φ D D' hD
  exact isCPMap_of_rig hG D'.P.isAb (CP.ofDegPre hG D) (CP.ofDegPre hG D')
    (fun T x y => Over.OverMorphism.ext ((pull_grp hD).2 T x y _ _ rfl rfl).symm) hD.w hD.w_gen hD.he
    ((maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig)

end GlobalTheory.DegPullPackage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsGrpPullbackOfEqId
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.SelfCmp

theorem isGrpPullback_of_eq_id {S : Scheme.{0}} (G : Over S) [GrpObj G] {f : S ⟶ S} (hf : f = 𝟙 S) :
    IsGrpPullback G G f (𝟙 G.left) := by
  subst hf
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end GlobalTheory.LN.SelfCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointExtendsTorsionPointMul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

theorem grpPullback_mul_section {B B' : Scheme.{0}} {G : Over B} {G' : Over B'} [GrpObj G] [GrpObj G']
    {f : B' ⟶ B} {φ : G'.left ⟶ G.left} (H : IsGrpPullback G' G f φ) (x y : baseOver B' ⟶ G')
    (h h' : baseOver B ⟶ G) (hx : x.left ≫ φ = f ≫ h.left) (hy : y.left ≫ φ = f ≫ h'.left) :
    (x * y).left ≫ φ = f ≫ (h * h').left := by
  let U : Over.mk ((baseOver B').hom ≫ f) ⟶ baseOver B := Over.homMk f (by simp)
  have e := H.2 (baseOver B') x y (U ≫ h) (U ≫ h') hx.symm hy.symm
  rw [← MonObj.comp_mul] at e
  exact e.symm

theorem extends_mul (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ)
    [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a b : S.Gam) (h h' : baseOver (Sp u.V) ⟶ u.G)
    (ha : Extends u a h) (hb : Extends u b h') : Extends u (a + b) (h * h') := by
  obtain ⟨x, x1, x2, x3⟩ := ha
  obtain ⟨y, y1, y2, y3⟩ := hb
  have := u.U.gen_hom
  let X : baseOver (Sp (FractionRing u.V)) ⟶ (Over.pullback (jK u.V)).obj u.G := Over.homMk x x2
  let Y : baseOver (Sp (FractionRing u.V)) ⟶ (Over.pullback (jK u.V)).obj u.G := Over.homMk y y2
  refine ⟨(X * Y).left, ?_, Over.w (X * Y), ?_⟩
  · exact grpPullback_mul_section (isGrpPullback_pullback u.G (jK u.V)) X Y h h' x1 y1
  · rw [ρ.pt_add]
    exact grpPullback_mul_section
      (((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl) X Y _ _ x3 y3

end GlobalTheory.UnitTheta
end

