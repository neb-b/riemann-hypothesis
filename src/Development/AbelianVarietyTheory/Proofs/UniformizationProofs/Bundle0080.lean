module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0071
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBalPow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSubSum
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ConvOfProd

theorem sum_conv {X A : Type} [AddCommGroup X] [CommRing A] (s s' S : Finset X) (F G : X → A)
    (hG : ∀ v ∉ s', G v = 0) (hS : ∀ β ∈ s, ∀ v ∈ s', β + v ∈ S) :
    ∑ α ∈ S, ∑ β ∈ s, F β * G (α - β) = (∑ β ∈ s, F β) * ∑ v ∈ s', G v := by
  classical
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [← Finset.mul_sum]
  congr 1
  symm
  refine Finset.sum_bij_ne_zero (fun v _ _ => β + v) (fun v h _ => hS β hβ v h)
    (fun a _ _ b _ _ e => add_left_cancel e) (fun α _ h => ?_) (fun v _ _ => by rw [add_sub_cancel_left])
  exact ⟨α - β, by by_contra hn; exact h (hG _ hn), h, add_sub_cancel β α⟩

theorem exists_sub_sum {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {Ix : Type}
    (S : LB.Sec (LB.LinComb L φ ε)) (p : Ix → LB.Sec (LB.LinComb L φ ε)) (s : Finset Ix) :
    ∃ d : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval d r z J = sval S r z J - ∑ i ∈ s, sval (p i) r z J := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S, fun Z r z J _ => by rw [Finset.sum_empty, sub_zero]⟩
  | insert i s hi ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨DVR.SecOps.secAdd d (DVR.SecOps.secNeg (p i)), fun Z r z J hJ => ?_⟩
    have hm := hJ.mem φ r
    have e : sval (DVR.SecOps.secAdd d (DVR.SecOps.secNeg (p i))) r z J = sval d r z J - sval (p i) r z J := by
      refine (gs_add r z _ hm _ _).trans ?_
      rw [sub_eq_add_neg]
      congr 1
      refine (gs_eq r z _ hm _).trans (Eq.trans ?_ (congrArg Neg.neg (gs_eq r z _ hm _)).symm)
      exact (congrArg _ (map_neg _ _)).trans (map_neg _ _)
    rw [e, hd Z r z J hJ, Finset.sum_insert hi]
    ring

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem over_eq {e : ℕ} (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of R))} {Z : Scheme.{0}}
    (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (T ⊗ D.P.A).left) (hr : r ≫ (snd T D.P.A).left = x ≫ g.pG.left) :
    x ≫ ((Over.map (thick R I e)).obj (thickObj R I e G)).hom = r ≫ (T ⊗ D.P.A).hom := by
  rw [← Over.w g.pG, ← Over.w (snd T D.P.A), ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ D.P.A.hom) hr.symm

theorem prod_mul_coord {e : ℕ} (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of R))} {k l m : ℕ} {β ga α : D.X}
    (hα : β + ga = α) {a : SecBT D T k β} {b : SecBT D T l ga} {c : SecBT D T m α} (H : IsProdB a b c) {Z : Scheme.{0}}
    (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (T ⊗ D.P.A).left) (hr : r ≫ (snd T D.P.A).left = x ≫ g.pG.left)
    (z : Z) (J) (hJ : Good D.P.L z J) :
    sval c r z J * (val (g.t α) x z J).val =
      sval a r z J * (val (g.t β) x z J).val * (sval b r z J * (val (g.t ga) x z J).val) := by
  subst hα
  let FinalForm : Over (Spec (CommRingCat.of R)) := Over.mk (r ≫ (T ⊗ D.P.A).hom)
  let ro : FinalForm ⟶ T ⊗ D.P.A := Over.homMk r rfl
  let xo : FinalForm ⟶ (Over.map (thick R I e)).obj (thickObj R I e G) := Over.homMk x (over_eq g x r hr)
  have h₁ := H FinalForm ro z J hJ
  have h₂ := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (g.t_mul β ga) x).trans (val_mul hJ _ _ _))
  have h₃ := val_cub D.cub xo (z := z) hJ (DVR.cP D _ β) (DVR.cP D _ ga) g.pG
  have h₄ : xo ≫ g.pG = ro ≫ snd T D.P.A := Over.OverMorphism.ext hr.symm
  rw [DVR.comp_cP, DVR.comp_cP, h₄] at h₃
  have h₅ := congrArg Units.val ((congrArg (val (g.t (β + ga)) x z J * ·) h₃).symm.trans h₂)
  rw [Units.val_mul, Units.val_mul] at h₅
  refine (congrArg (· * (val (g.t (β + ga)) x z J).val) h₁).trans ?_
  rw [_root_.mul_mul_mul_comm, ← h₅]
  exact (_root_.mul_assoc _ _ _).trans (congrArg _ (mul_comm _ _))

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k l : ℕ) (f : ∀ α, SecBT D T k α) (g : ∀ α, SecBT D T l α) (h : ∀ α, SecBT D T (k + l) α) (σ : U.SecGT T (k + l)), U.ProdExp T f g σ → U.ExpT T (k + l) σ h → ConvT I f g h := by
  intro R _ _ I D A G _ _ U T k l f g h σ hP hE α₀
  classical
  choose p hp using fun α β => exists_isProdB R D T k l β (α - β) α (add_sub_cancel β α) (f β) (g (α - β))
  refine ⟨p α₀, hp α₀, fun e => ?_⟩
  obtain ⟨s, s', hP⟩ := hP e
  obtain ⟨s'', hE⟩ := hE e
  have key : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (T ⊗ D.P.A).left),
      r ≫ (snd T D.P.A).left = x ≫ (U.gt e).pG.left → ∀ (z : Z) (J), Good D.P.L z J →
      (∀ α ∉ s, sval (f α) r z J = 0) ∧ (∀ α ∉ s', sval (g α) r z J = 0) ∧ (∀ α ∉ s'', sval (h α) r z J = 0) ∧
      ∑ α ∈ s'', sval (h α) r z J * (val ((U.gt e).t α) x z J).val =
        (∑ α ∈ s, sval (f α) r z J * (val ((U.gt e).t α) x z J).val) *
          ∑ α ∈ s', sval (g α) r z J * (val ((U.gt e).t α) x z J).val := by
    intro Z x r hr z J hJ
    let FinalForm : Over (Spec (CommRingCat.of R)) := Over.mk (r ≫ (T ⊗ D.P.A).hom)
    let ro : FinalForm ⟶ T ⊗ D.P.A := Over.homMk r rfl
    let xo : FinalForm ⟶ (Over.map (thick R I e)).obj (thickObj R I e G) := Over.homMk x (over_eq (U.gt e) x r hr)
    let rG : FinalForm ⟶ T ⊗ G := lift (ro ≫ fst _ _) (xo ≫ fstG I e G)
    have e₁ : rG.left ≫ (snd T G).left = x ≫ (fstG I e G).left := congrArg (fun q : FinalForm ⟶ G => q.left) (lift_snd _ _)
    have e₂ : r ≫ (fst T D.P.A).left = rG.left ≫ (fst T G).left :=
      congrArg (fun q : FinalForm ⟶ T => q.left) (lift_fst (ro ≫ fst _ _) (xo ≫ fstG I e G)).symm
    choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
    obtain ⟨a₁, a₂, a₃⟩ := hP Z x rG.left r e₁ hr e₂ z JG J hJG hJ
    obtain ⟨b₁, b₂⟩ := hE Z x rG.left r e₁ hr e₂ z JG J hJG hJ
    exact ⟨a₁, a₂, b₁, b₂.symm.trans a₃⟩
  choose d hd using fun α => exists_sub_sum (h α) (p α) s
  let S : Finset D.X := insert α₀ (s'' ∪ Finset.image₂ (· + ·) s s')
  have hd0 := GlobalTheory.sval_eq_zero_of_sum_mul_coord R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) (Fin 4)
    (famφT D T) (DegPre.famε (k + l)) d S (fun Z x r hr z J hJ => by
      obtain ⟨-, k₂, k₃, k₄⟩ := key Z x r hr z J hJ
      have c := sum_conv s s' S (fun β => sval (f β) r z J * (val ((U.gt e).t β) x z J).val)
        (fun β => sval (g β) r z J * (val ((U.gt e).t β) x z J).val)
        (fun v hv => by rw [k₂ v hv, zero_mul])
        (fun β hβ v hv => Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image₂_of_mem hβ hv)))
      have c' : ∑ α ∈ s'', sval (h α) r z J * (val ((U.gt e).t α) x z J).val =
          ∑ α ∈ S, sval (h α) r z J * (val ((U.gt e).t α) x z J).val :=
        Finset.sum_subset (fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_left _ ha))
          (fun a _ ha => by rw [k₃ a ha, zero_mul])
      rw [← sub_eq_zero.2 (c'.symm.trans (k₄.trans c.symm)), ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [hd α Z r z J hJ, sub_mul, Finset.sum_mul]
      exact congrArg _ (Finset.sum_congr rfl fun β _ =>
        prod_mul_coord (U.gt e) (add_sub_cancel β α) (hp α β) x r hr z J hJ)) α₀ (Finset.mem_insert_self _ _)
  refine ⟨s, fun Z r hl z J hJ => ⟨fun β hβ => ?_, ?_⟩⟩
  · refine GlobalTheory.LiftTest.main R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) _ D.P.L D.P.isLB _ _ _ (p α₀ β)
      (fun Z x r hr z J hJ => ?_) Z r hl z J hJ
    have c := prod_mul_coord (U.gt e) (add_sub_cancel β α₀) (hp α₀ β) x r hr z J hJ
    rw [(key Z x r hr z J hJ).1 β hβ, zero_mul, zero_mul] at c
    exact (Units.mul_left_eq_zero _).1 c
  · have c := GlobalTheory.LiftTest.main R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) _ D.P.L D.P.isLB _ _ _ (d α₀) hd0 Z r hl z J hJ
    rw [hd α₀ Z r z J hJ] at c
    exact sub_eq_zero.1 c

end GlobalTheory.ConvOfProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistConvNeZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.TwistNonvan

theorem sval_scale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top (hJ.mem _ r) _) rfl)

theorem sval_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s r z J = 0 := by
  refine (congrArg (gs r z _) (hs _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

theorem exists_constHom {W : Type} [CommRing W] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of W)) (r : Z ⟶ Y)
    (z : Z) : ∃ c : W →+* Z.presheaf.stalk z, ∀ w, gs r z ⊤ (scal p w) = c w :=
  ⟨((Z.presheaf.germ (r ⁻¹ᵁ ⊤) z trivial).hom.comp (r.app ⊤).hom).comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom), fun w => gs_eq r z ⊤ trivial _⟩

theorem sum_eq_zero {V : Type} [CommRing V] [IsDomain V] (I : Ideal V) (D : DegPre V) (k : ℕ) (α : D.X)
    {W : Type} [CommRing W] [Algebra V W] (a : Multiplicative D.X →* Wˣ)
    (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α) (h : ∀ α, SecBT D (TA V W) (k + 1) α)
    (hc : ConvT I (twist a f') (twist (a ^ k)⁻¹ g') h) (h0 : ∀ j, (h α).f j = 0) (e : ℕ)
    (Z : Over (Spec (CommRingCat.of V))) (r : Z ⟶ TA V W ⊗ D.P.A) (hl : Lvl I e Z.hom) (z : Z.left) (J)
    (hJ : Good D.P.L z J) (s : Finset D.X) (hs : ∀ β ∉ s, sval (f' β) r.left z J = 0)
    (c : W →+* Z.left.presheaf.stalk z) (hcw : ∀ w, gs r.left z ⊤ (scal (R := W) (fst (TA V W) D.P.A).left w) = c w) :
    ∑ β ∈ s, c (a (Multiplicative.ofAdd ((k + 1) • β - k • α))).val * (sval (f' β) r.left z J *
      sval (g' (α - β)) r.left z J *
      (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c (α - β)) (r ≫ snd _ D.P.A)).val) = 0 := by
  classical
  obtain ⟨p, hp, hsum⟩ := hc α
  obtain ⟨s', hs'⟩ := hsum e
  obtain ⟨h₁, h₂⟩ := hs' Z.left r.left (by rw [Over.w r]; exact hl) z J hJ
  have hT : ∀ β, sval (p β) r.left z J = c (a (Multiplicative.ofAdd ((k + 1) • β - k • α))).val *
      (sval (f' β) r.left z J * sval (g' (α - β)) r.left z J *
      (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c (α - β)) (r ≫ snd _ D.P.A)).val) := fun β => by
    have e₁ : a (Multiplicative.ofAdd ((k + 1) • β - k • α)) =
        a (Multiplicative.ofAdd β) * (a ^ k)⁻¹ (Multiplicative.ofAdd (α - β)) := by
      rw [MonoidHom.inv_apply, MonoidHom.pow_apply, ← map_pow, ← map_inv, ← map_mul]
      congr 1
      rw [← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
      congr 1
      module
    rw [hp β Z r z J hJ, e₁, Units.val_mul, map_mul]
    unfold twist
    rw [sval_scale _ _ _ z hJ, sval_scale _ _ _ z hJ, hcw, hcw]
    ring
  rw [sval_zero _ h0 _ z hJ] at h₂
  rw [← Finset.sum_congr rfl (fun β _ => hT β)]
  rw [Finset.sum_subset (Finset.subset_union_left (s₂ := s')) (fun β _ hβ => by rw [hT β, hs β hβ]; ring),
    ← Finset.sum_subset (Finset.subset_union_right (s₁ := s)) (fun β _ hβ => h₁ β hβ)]
  exact h₂.symm

theorem exists_level {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (D : DegPre V)
    {k l m : ℕ} {β ga α : D.X} (f : SecBT D (𝟙_ _) k β) (g : SecBT D (𝟙_ _) l ga) (p : SecBT D (𝟙_ _) m α)
    (hp : IsProdB f g p) (hf : ∃ j, f.f j ≠ 0) (hg : ∃ j, g.f j ≠ 0) :
    ∃ e : ℕ, ¬ ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
      Lvl (IsLocalRing.maximalIdeal V) e (r ≫ (𝟙_ _ ⊗ D.P.A).hom) → ∀ (z : Z) (J), Good D.P.L z J →
        sval p r z J = 0 := by
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (𝟙_ (Over (Spec (CommRingCat.of V)))).left :=
    (inferInstance : IsIntegral (Spec (CommRingCat.of V)))
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of V)))).left :=
    (inferInstance : IsAffine (Spec (CommRingCat.of V)))
  let i : V ≃+* Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of V)).symm.commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, ⊤) := isNoetherianRing_of_ringEquiv V i
  have := GlobalTheory.isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (𝟙_ _)
  obtain ⟨j, hj⟩ := GlobalTheory.exists_ne_zero_of_sval_eq_mul_unit _ _ D.P.L D.P.isLB _ _ _ _ _ _ _ _ _ f g p
    (fun y J hJ => ⟨_, hp (𝟙_ _ ⊗ D.P.A) (𝟙 _) y J hJ⟩) hf hg
  by_contra hne
  refine hj (GlobalTheory.sec_eq_zero_of_sval_finite_level V (IsLocalRing.maximalIdeal V) (𝟙_ _) D.P.A (fun r hr => ?_) _ D.P.L
    D.P.isLB _ _ _ p (fun e => by
      by_contra h
      exact hne ⟨e, h⟩) j)
  have e : scal (𝟙_ (Over (Spec (CommRingCat.of V)))).hom r = i r := rfl
  rw [e, Ideal.mem_jacobson_bot]
  intro y
  obtain ⟨y, rfl⟩ := i.surjective y
  rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.mem_jacobson_bot] at hr
  have := (hr y).map i
  rwa [map_add, map_mul, map_one] at this

end GlobalTheory.UU.TwistNonvan

namespace GlobalTheory.UU
open TwistNonvan

theorem exists_twist_conv_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V) (k : ℕ) (f : ∀ α, SecBT D (𝟙_ _) k α) (g : ∀ α, SecBT D (𝟙_ _) 1 α) (α β₀ : D.X), NullFam (IsLocalRing.maximalIdeal V) f → (∃ j, (f β₀).f j ≠ 0) → (∃ j, (g (α - β₀)).f j ≠ 0) → ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (_ : Algebra V W) (φ : TF (R := V) (Kbar V) ⟶ TA V W) (a : Multiplicative D.X →* Wˣ), FinExt V W ∧ Function.Injective φ.left.appTop.hom ∧ ∀ (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α) (h : ∀ α, SecBT D (TA V W) (k + 1) α), PullT (toUnit _) f f' → PullT (toUnit _) g g' → ConvT (IsLocalRing.maximalIdeal V) (twist a f') (twist (a ^ k)⁻¹ g') h → ∃ j, (h α).f j ≠ 0 := by
  intro V _ _ _ hV D k f g α β₀ hnull hf hg
  classical
  obtain ⟨hd, hcpl, hch⟩ := hV
  obtain ⟨p, hp⟩ := exists_isProdB V D (𝟙_ _) k 1 β₀ (α - β₀) α (by abel) (f β₀) (g (α - β₀))
  obtain ⟨e, he⟩ := exists_level D _ _ p hp hf hg
  obtain ⟨s₀, hs₀⟩ := hnull e
  obtain ⟨⟨n, hn, hnu⟩, hcyc⟩ := GlobalTheory.exists_finite_extension_primitive_residue V
  let u : D.X → D.X := fun β => (k + 1) • β - k • α
  have hu : Function.Injective u := fun x y hxy => by
    have h₁ : ((k + 1 : ℕ) : ℤ) • x = ((k + 1 : ℕ) : ℤ) • y := by
      rw [natCast_zsmul, natCast_zsmul]; exact sub_left_injective hxy
    exact smul_right_injective D.X (by positivity) h₁
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.laurent_coeff_eq_zero_of_vanish_torsion D.X n hn ((insert β₀ s₀).image u)
  obtain ⟨W, iW, iL, iA, φ, ζ, hW, hφ, hnW, hζ, hprim⟩ := hcyc n j₀ hn hnu
  by_contra hne
  have H : ∀ a : Multiplicative D.X →* Wˣ, ∃ (f' : ∀ α, SecBT D (TA V W) k α) (g' : ∀ α, SecBT D (TA V W) 1 α)
      (h : ∀ α, SecBT D (TA V W) (k + 1) α), PullT (toUnit _) f f' ∧ PullT (toUnit _) g g' ∧
      ConvT (IsLocalRing.maximalIdeal V) (twist a f') (twist (a ^ k)⁻¹ g') h ∧ ∀ j, (h α).f j = 0 := fun a => by
    by_contra hh
    refine hne ⟨W, iW, iL, iA, φ, a, hW, hφ, fun f' g' h h₁ h₂ h₃ => ?_⟩
    by_contra h₄
    exact hh ⟨f', g', h, h₁, h₂, h₃, fun j => by_contra fun h₅ => h₄ ⟨j, h₅⟩⟩
  obtain ⟨hfin, hfree, hdom, -, -⟩ := hW
  refine he (GlobalTheory.sval_eq_zero_of_faithfullyFlat_base V W (IsLocalRing.maximalIdeal V) e (𝟙_ _ ⊗ D.P.A) _ D.P.L
    D.P.isLB _ _ _ p ?_)
  intro Z r ω hω hl z J hJ
  let Z' : Over (Spec (CommRingCat.of V)) := Over.mk (r ≫ (𝟙_ _ ⊗ D.P.A).hom)
  let rr : Z' ⟶ 𝟙_ _ ⊗ D.P.A := Over.homMk r rfl
  let ωω : Z' ⟶ TA V W := Over.homMk ω hω
  let r' : Z' ⟶ TA V W ⊗ D.P.A := lift ωω (rr ≫ snd _ _)
  have e₁ : r' ≫ toUnit _ ▷ D.P.A = rr := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · simp [r']
  have e₂ : r'.left ≫ (toUnit (TA V W) ▷ D.P.A).left = rr.left := congrArg (fun q => q.left) e₁
  have e₃ : r' ≫ snd _ _ = rr ≫ snd _ _ := lift_snd _ _
  obtain ⟨c, hc⟩ := exists_constHom (W := W) (fst (TA V W) D.P.A).left r'.left z
  let T : D.X → Z'.left.presheaf.stalk z := fun β => sval (f β) rr.left z J * sval (g (α - β)) rr.left z J *
      (cubV D.cub (T := Z') z J (toUnit Z' ≫ D.c β) (toUnit Z' ≫ D.c (α - β)) (rr ≫ snd _ D.P.A)).val
  have e₄ : sval p rr.left z J = T β₀ := hp Z' rr z J hJ
  letI : Module W (Z'.left.presheaf.stalk z) := Module.compHom _ c
  have key := hj₀ j₀ le_rfl W ζ hnW hζ hprim (Z'.left.presheaf.stalk z) (Function.extend u T 0) (fun a _ => by
    obtain ⟨f', g', h, h₁, h₂, h₃, h₄⟩ := H a
    have v₁ : ∀ β, sval (f' β) r'.left z J = sval (f β) rr.left z J := fun β =>
      (h₁ β _ r'.left z J hJ).trans (by rw [e₂])
    have v₂ : ∀ β, sval (g' β) r'.left z J = sval (g β) rr.left z J := fun β =>
      (h₂ β _ r'.left z J hJ).trans (by rw [e₂])
    have := sum_eq_zero _ D k α a f' g' h h₃ h₄ e Z' r' hl z J hJ (insert β₀ s₀) (fun β hβ =>
      (v₁ β).trans (hs₀ β (fun hb => hβ (Finset.mem_insert_of_mem hb)) Z r hl z J hJ)) c hc
    rw [Finset.sum_image (fun x _ y _ hxy => hu hxy)]
    refine Eq.trans (Finset.sum_congr rfl fun β _ => ?_) this
    rw [hu.extend_apply, v₁, v₂, e₃]
    rfl) (u β₀) (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _))
  rw [hu.extend_apply] at key
  exact e₄.trans key

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamilyFunctionalEquationFieldChange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory
namespace FieldChange

theorem sval_extend {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {φ₁ : K → (Y' ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (hφ : φ₁ = fun k => h ≫ φ k)
    (s : LB.Sec (LB.LinComb L φ₁ ε)) (f : LB.Sec (LB.LinComb L φ ε))
    (H : ∀ y J, Good L y J → sval s (𝟙 _) y J = sval f h y J) {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (J)
    (hJ : Good L z J) : sval s r z J = sval f (r ≫ h) z J := by
  subst hφ
  have e := sec_ext_val hL (s := s) (s' := DVR.pullSec L φ ε f h) (fun y J hJ => by
    rw [DVR.SectionScalarValuation.sval_pullSec φ ε f h _ y hJ, Category.id_comp]; exact H y J hJ)
  rw [← DVR.SectionScalarValuation.sval_pullSec φ ε f h r z hJ]
  exact congrArg (gs r z _) (e _)

theorem gs_scal_comp {R : Type} [CommRing R] {Y Y' Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (h : Y' ⟶ Y)
    (r : Z ⟶ Y') (z : Z) (c : R) : gs (r ≫ h) z ⊤ (scal p c) = gs r z ⊤ (scal (h ≫ p) c) :=
  (gs_pull r h z ⊤ (by trivial) _).symm

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem fam_comp (φ : TF (R := R) F ⟶ T) (α : D.X) :
    DegPre.famφ D F α = fun i => (φ ▷ D.P.A).left ≫ famφT D T α i := by
  have e₀ : φ ▷ D.P.A ≫ snd T D.P.A = snd _ _ := whiskerRight_snd _ _
  have e₂ : φ ▷ D.P.A ≫ DVR.cP D _ α = DVR.cP D _ α := DVR.comp_cP D _ α
  funext i
  fin_cases i
  · exact (congrArg (fun q => q.left) e₀).symm
  · refine (congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left)
      ((MonObj.comp_mul (φ ▷ D.P.A) (snd T D.P.A) (DVR.cP D _ α)).trans ?_)).symm
    rw [e₀, e₂]; rfl
  · exact (congrArg (fun q => q.left) e₂).symm
  · exact (congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (φ ▷ D.P.A))).symm

theorem tr_comp (φ : TF (R := R) F ⟶ T) (mu : D.X) :
    φ ▷ D.P.A ≫ trT D (toUnit T ≫ D.c mu) = DegPre.trF D F mu ≫ φ ▷ D.P.A := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [trT, DegPre.trF]
  · rw [Category.assoc, Category.assoc, whiskerRight_snd, trT, DegPre.trF, lift_snd, lift_snd]
    refine (MonObj.comp_mul (φ ▷ D.P.A) (snd T D.P.A) (fst _ _ ≫ DVR.cP D _ mu)).trans ?_
    rw [whiskerRight_snd, DVR.comp_cP, DVR.comp_cP]; rfl

theorem pullB_all {φ : TF (R := R) F ⟶ T} {k : ℕ} {f : ∀ α, SecBT D T k α} {s : Raw D F k} (H : PullB D F φ k f s)
    (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J) (hJ : Good D.P.L z J) :
    sval (s α) r z J = sval (f α) (r ≫ (φ ▷ D.P.A).left) z J :=
  sval_extend D.P.isLB _ (fam_comp D φ α) (s α) (f α) (H α) r z J hJ

theorem isUnit_scal {c : R} (hc : c ≠ 0) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) :
    IsUnit (gs r z ⊤ (scal (DegPre.BF D F).hom c)) := by
  have e : (DegPre.BF D F).hom = ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) ≫ jK R := by
    rw [Category.assoc]; exact (Over.w (fst (TF (R := R) F) D.P.A)).symm
  have hu : IsUnit (scal (jK R) c) := by
    have n := congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
    have hc' : IsUnit (algebraMap R (FractionRing R) c) :=
      IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hc)
    exact (congrArg IsUnit n).mp (hc'.map _)
  rw [e, gs_eq _ _ ⊤ (by trivial)]
  exact ((hu.map ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F).appTop.hom).map _).map _

end FieldChange


open FieldChange in
theorem famFE_field_change : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] (k : ℕ) (f : ∀ α, SecBT D T k α) (F F' : Type) [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (φ : TF (R := R) F ⟶ T) (φ' : TF (R := R) F' ⟶ T) (s : Raw D F k) (s' : Raw D F' k), Function.Injective φ.left.appTop.hom → PullB D F φ k f s → PullB D F' φ' k f s' → DegPre.FamFE D F k s → DegPre.FamFE D F' k s' := by
  intro hG R _ _ _ D T _ k f F F' _ _ _ _ φ φ' s s' hinj hs hs' hfe mu α u' hu' hc'
  obtain ⟨u₀, r₁, r₂, hu₀, -, h₂, hv⟩ := GlobalTheory.UU.IntGen.main hG R D T k α mu
  obtain ⟨⟨u, hu, hc⟩, -⟩ := DVR.gen_fe (D := D) (F := F) hG k mu α
  have : Smooth D.P.A.hom := D.P.isAb.smooth
  have : IsAffine (TF (R := R) F).left := inferInstanceAs (IsAffine (Spec _))
  have sc : ∀ {E : Type} [Field E] [Algebra (FractionRing R) E] (ψ : TF (R := R) E ⟶ T) (c : R)
      (y : (DegPre.BF D E).left), gs (ψ ▷ D.P.A).left y ⊤ (scal (T ⊗ D.P.A).hom c) =
        gs (𝟙 _) y ⊤ (scal (DegPre.BF D E).hom c) := fun ψ c y => by
    rw [← Over.w (ψ ▷ D.P.A), ← gs_scal_comp, Category.id_comp]
  have tr : ∀ {E : Type} [Field E] [Algebra (FractionRing R) E] (ψ : TF (R := R) E ⟶ T),
      (ψ ▷ D.P.A).left ≫ (trT D (toUnit T ≫ D.c mu)).left = (𝟙 _ ≫ (DegPre.trF D E mu).left) ≫ (ψ ▷ D.P.A).left :=
    fun ψ => by rw [Category.id_comp]; exact congrArg (fun q => q.left) (tr_comp D ψ mu)
  have key := sec_relation_descends _ D.P.A T (TF (R := R) F) φ hinj _ _ D.P.L D.P.isLB _ _ _
    (famφT D T α) (DegPre.famε k) (famφT D T (α + k • mu)) (DegPre.famε k)
    (deltaφT D (α + k • mu) α (toUnit T ≫ D.c mu)) (DegPre.deltaε k) (trT D (toUnit T ≫ D.c mu)).left
    (f α) (f (α + k • mu)) u₀ (scal (T ⊗ D.P.A).hom r₁) (scal (T ⊗ D.P.A).hom r₂) hu₀
    (fun U _ h => by
      refine Eq.symm (Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
          (c := ∏ i, h ((trT D (toUnit T ≫ D.c mu)).left ≫ famφT D T α i) ^ DegPre.famε k i) rfl
          (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
            (c := ∏ i, h (famφT D T (α + k • mu) i) ^ DegPre.famε k i) rfl (DVR.prod_neg _ _ rfl))) ?_)
      exact (mul_comm _ _).trans (inv_mul_cancel_right _ _))
    (fun y J hJ => by
      have e₁ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (hfe mu α u hu hc) _ (𝟙 _) y J hJ
      have e₂ := hv F φ u hu hc _ (𝟙 _) y J hJ
      rw [Category.id_comp] at e₂
      rw [sc, sc, tr, ← pullB_all D hs α _ y J hJ, ← hs _ y J hJ, e₁, mul_left_comm, e₂, mul_left_comm])
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').2 fun y J hJ => ?_
  have e₁ := key _ (φ' ▷ D.P.A).left y J hJ
  have e₂ := hv F' φ' u' hu' hc' _ (𝟙 _) y J hJ
  rw [Category.id_comp] at e₂
  rw [sc, sc, tr, ← pullB_all D hs' α _ y J hJ, ← hs' _ y J hJ, mul_left_comm, ← e₂, mul_left_comm] at e₁
  exact (isUnit_scal D h₂ _ y).mul_left_cancel e₁

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointBalancedPowerLift
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TauBalElem

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.TauBalBox

theorem tau_zero_left {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {y : (TK R).left} {J}
    (hJ : Good D.P.L y J) (b : D.X) : val (D.tau 0 b) (𝟙 _) y J = 1 := by
  have C : IsCub (cubV D.cub (T := TK R) y J) := isCub_cubV D.cub hJ
  have t := tauK_mul hJ hB 0 0 b
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
  exact mul_eq_left.1 t.symm

end GlobalTheory.TauBalElem
end
end

