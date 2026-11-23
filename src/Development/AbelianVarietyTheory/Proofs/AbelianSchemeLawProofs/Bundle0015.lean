module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.SectionsGroupRank
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalExtendsAndExtendGen
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace CubeExtension

section Group

variable {S : Scheme.{0}}

theorem smooth_tensor (A B : Over S) [Smooth A.hom] [Smooth B.hom] : Smooth (A ⊗ B).hom := by
  change Smooth (pullback.fst A.hom B.hom ≫ A.hom)
  infer_instance

theorem geometricallyConnected_tensor (A B : Over S) [Smooth A.hom] [Smooth B.hom]
    [GeometricallyConnected A.hom] [GeometricallyConnected B.hom] :
    GeometricallyConnected (A ⊗ B).hom := by
  change GeometricallyConnected (pullback.fst A.hom B.hom ≫ A.hom)
  exact GeometricallyConnected.comp _ _

variable (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem eSec_comp : eSec G ≫ G.hom = 𝟙 S := Over.w η[G]

theorem eSec_three :
    eSec (G3 G) = (lift (1 : 𝟙_ (Over S) ⟶ G) (lift (1 : 𝟙_ (Over S) ⟶ G) (1 : 𝟙_ (Over S) ⟶ G))).left := by
  unfold eSec
  congr 1
  ext <;> simp [Hom.one_def]

theorem formEq_origin :
    FormEq (K := PEmpty) (PEmpty.elim : PEmpty → ((𝟙_ (Over S)).left ⟶ G.left)) PEmpty.elim
      (fun I => eSec (G3 G) ≫ thφ G (x3 G) I) thε := by
  intro U _ h
  rw [eSec_three, prod_cub]
  simp

end Group

theorem pullGen_genPull {X Y Z : Scheme.{0}} (M : LB X) (c : LB.Gen M) (f : Y ⟶ X) (h : Z ⟶ Y) :
    LB.pullGen M _ _ (LB.genPull M c f) h = LB.genPull M c (h ≫ f) := by
  refine lbGen_ext fun j => congrArg Units.val ?_
  exact LB.pull_res_comp h f _ _ _ _ _

end CubeExtension

open CubeExtension

theorem cubical_extends_of_extension
    (h₁ : (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f))
    (h₂ : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (H X : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K)), eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => pullback.fst p (etaK V K) ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K)) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c (pullback.fst p (etaK V K)) = t)) : Semi.cubical_extendsSt.{0} := by
  intro V _ _ _ K _ _ _ G _ _ _ _ _ _ eA heA L t hc ht
  have s₂ := smooth_tensor G G
  have s₃ := smooth_tensor G (G ⊗ G)
  have c₂ := geometricallyConnected_tensor G G
  have c₃ := geometricallyConnected_tensor G (G ⊗ G)
  obtain ⟨ρ, hρ, hv⟩ := exists_gen L.isLB (formEq_origin G) (LB.oneGen L.L) (LB.isGen_oneGen L.L)
  refine h₂ V K (G3 G).left G.left (G3 G).hom (eSec (G3 G)) s₃ (h₁ _ _ _ s₃ c₃) (eSec_comp _) eA heA
    L.L L.isLB thK (thφ G (x3 G)) thε t ρ ht hρ (corr_of_val L.isLB fun y J hJ => ?_)
  refine (val_corr hJ hc (𝟙 _)).trans ((val_one _).trans (Eq.symm ?_))
  exact (val_pull hJ ρ _ _).trans ((hv _ _ y J hJ).trans (val_one _))

theorem extendGen_of_extension
    (h₁ : (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f))
    (h₂ : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (H X : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K)), eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => pullback.fst p (etaK V K) ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K)) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c (pullback.fst p (etaK V K)) = t)) : Semi.extendGenSt.{0} := by
  intro V _ _ _ K _ _ _ G _ _ _ _ _ _ eA heA N r hr hc
  obtain ⟨c, ⟨hc₁, hc₂⟩, hu⟩ := h₂ V K G.left G.left G.hom (eSec G) inferInstance
    (h₁ _ _ _ inferInstance inferInstance) (eSec_comp _) eA heA N.L N.isLB PUnit (fun _ => 𝟙 _)
    (fun _ => 1) r N.rig hr N.rigGen hc
  obtain ⟨r', ⟨h₃, h₄⟩, hu'⟩ := existsUnique_genPull_eq (𝟙 G.left)
    (fun _ => Function.bijective_id) N.L c hc₁
  refine ⟨r', ⟨h₃, ?_⟩, fun r'' ⟨h₅, h₆⟩ => hu' r'' ⟨h₅, hu _ ⟨LB.isGen_genPull _ _ h₅ _, ?_⟩⟩⟩
  · rw [← h₄, pullGen_genPull] at hc₂
    exact hc₂
  · rw [pullGen_genPull]
    exact h₆

theorem cubical_extends_and_extendGen :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) →
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (H X : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K)), eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => pullback.fst p (etaK V K) ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K)) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c (pullback.fst p (etaK V K)) = t) →
    Semi.cubical_extendsSt.{0} ∧ Semi.extendGenSt.{0} :=
  fun h₁ h₂ => ⟨cubical_extends_of_extension h₁ h₂, extendGen_of_extension h₁ h₂⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FunEqZeroOfAffine
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.VVCompare

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SectionsGroupRank

section General

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem wchart_le_of_eq {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k)
    (j : K → L.ι) : LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k

def pullTo {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) : LB.Sec (LB.LinComb L φ' ε) where
  f j := (Y'.presheaf.map (homOfLE (wchart_le_of_eq h e j)).op).hom ((h.app _).hom (s.f j))
  compat := by
    obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
    exact (H1.SectionArithmetic.pullSec s h).compat

theorem sval_pullTo {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval (pullTo s h e) r z J = sval s (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact H1.SectionArithmetic.sval_pullSec s h r z hJ

end General

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}

omit [GrpObj A] in
theorem whisker_snd_left {T T' : Over S} (h : T' ⟶ T) :
    (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := by
  rw [← Over.comp_left, whiskerRight_snd]

abbrev pullS (a : ℤ) {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) : LB.Sec (LPow A L a T') :=
  pullSec (A := A) (L := L) (a := a) h s

abbrev sv {a : ℤ} {T : Over S} (s : LB.Sec (LPow A L a T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : Z.presheaf.stalk z :=
  sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s r z J

theorem sv_pullS (a : ℤ) {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T' ⊗ A).left) (z : Z) {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    sv A (pullS A a h s) r z J = sv A s (r ≫ (h ▷ A).left) z J :=
  sval_pullTo (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (h ▷ A).left
    (fun _ => whisker_snd_left A h) r z hJ

section Twist

variable {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
  {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}

theorem sv_of_isTwistPull {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (H : IsTwistPull A L ψ m hm a b α s s') {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    sv A s' r z J = (val α r z J).val * sv A s (r ≫ ψ.left) z J := by
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  have hz := hJ.mem ![(snd T A).left, m.left] r
  have key : ∀ j : Fin 2 → L.ι, r z ∈ LB.wchart L ![(snd T A).left, m.left] j →
      gs r z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0)) (s'.f (fun _ => j 0)) =
        (gm r z (LB.wchart L ![(snd T A).left, m.left] j) (α.s j)).val *
          gs (r ≫ ψ.left) z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
            (s.f (fun _ => j 1)) := fun j hz =>
    (gs_res r z _ hz _).symm.trans ((congrArg (gs r z _) (H j)).trans ((gs_mul r z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_unit r z _ hz _) ((gs_res r z _ hz _).trans
        (gs_pull r ψ.left z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
          (chart_le_pull A L ψ m hm j hz) _)))))
  have e₁ := sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J
    (fun _ => J (r ≫ m.left)) (fun _ => by rw [Category.assoc, e])
  exact (key _ hz).trans (congrArg _ e₁.symm)

theorem isTwistPull_of_sv (hL : L.IsLB) (hα : α.IsGen) {s : LB.Sec (LPow A L b T)}
    {s' : LB.Sec (LPow A L a T)}
    (H : ∀ y J, Good L y J → sv A s' (𝟙 _) y J = (val α (𝟙 _) y J).val * sv A s (𝟙 _ ≫ ψ.left) y J) :
    IsTwistPull A L ψ m hm a b α s s' := by
  intro j
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  refine fn_ext fun y hy => ?_
  choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
  have h0 := chart_le_zero A L m j hy
  have h1 := chart_le_pull A L ψ m hm j hy
  refine (gs_res _ y _ hy _).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_unit _ y _ hy _) ((gs_res _ y _ hy _).trans
      (gs_pull _ ψ.left y _ h1 _)))).symm)
  refine (sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) y h0
    (Good.mem hJ _ _)).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val (gen_trans hα (𝟙 _) y hy (Good.mem hJ _ _)))
    (sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) y h1
    (Good.mem hJ _ _))).symm
  refine (congrArg _ (H y J hJ)).trans ?_
  rw [Units.val_mul]
  refine Eq.trans ?_ (_root_.mul_mul_mul_comm _ _ _ _)
  rw [← Units.val_mul]
  refine congrArg₂ (· * ·) (congrArg Units.val ?_) rfl
  have e' : (𝟙 _ ≫ ψ.left) ≫ (snd T A).left = 𝟙 _ ≫ m.left := by rw [Category.assoc, e]
  simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, zpow_neg]
  rw [e']
  exact (inv_mul_cancel_right _ _).symm

theorem exists_isTwistPull (hL : L.IsLB) (hα : α.IsGen) (s : LB.Sec (LPow A L b T)) :
    ∃ s' : LB.Sec (LPow A L a T), IsTwistPull A L ψ m hm a b α s s' := by
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T A).left) (ε' := fun _ => a)
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
        e, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, mul_inv_cancel_comm_assoc])
    (pullMulSec (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s ψ.left α hα)
  exact ⟨s', isTwistPull_of_sv A hL hα fun y J hJ =>
    (hs' _ _ y J hJ).trans ((sval_pullMulSec _ _ α hα _ y hJ).trans (mul_comm _ _))⟩

end Twist

theorem exists_isActOf (hL : L.IsLB) {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T)
    (s : LB.Sec (LPow A L k T)) : ∃ s', IsActOf A L k θ s s' :=
  exists_isTwistPull A hL θ.isGen s

section Pull

variable {A} {a : ℤ} {T T' T'' : Over S}

end Pull

section VV

variable (P : PolAV S) (N m : ℕ) {T T' : Over S}

variable {κ : Type} [Fintype κ]

variable {P N m}

end VV

variable (P : PolAV S) (N m : ℕ)

end GlobalTheory.VVCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulPull

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

def HasGen {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen

section

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}

theorem HasGen.mul (h : HasGen L φ ε) (h' : HasGen L φ' ε') :
    HasGen L (Sum.elim φ φ') (Sum.elim ε ε') := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht'⟩ := h'
  exact ⟨_, DVR.mulGen_isGen L _ _ _ _ t t' ht ht'⟩

theorem HasGen.inv (h : HasGen L φ ε) : HasGen L φ (fun k => -ε k) := by
  obtain ⟨t, ht⟩ := h
  exact ⟨_, DVR.invGen_isGen L _ _ t ht⟩

theorem HasGen.pull (h : HasGen L φ ε) (f : Z ⟶ Y) : HasGen L (fun k => f ≫ φ k) ε := by
  obtain ⟨t, ht⟩ := h
  exact ⟨_, DVR.pullGen_isGen L _ _ t ht f⟩

theorem HasGen.of_formEq (hL : L.IsLB) (h : HasGen L φ ε) (e : FormEq φ ε φ' ε') : HasGen L φ' ε' := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht', -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hL e t ht
  exact ⟨t', ht'⟩

end

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem hasGen_pow (hL : L.IsLB) (hcube : HasGen L (thφ A (x3 A)) thε) {T : Over S} (x : T ⟶ A)
    (hone : HasGen L (K := Fin 1) ![(1 : T ⟶ A).left] ![1])
    (hsym : HasGen L (K := Fin 2) ![x.left, (x⁻¹).left] ![1, -1]) (n : ℕ) :
    HasGen L (K := Fin 2) ![x.left, (x ^ n).left] ![(n : ℤ) ^ 2, -1] := by
  induction n using Nat.twoStepInduction with
  | zero =>
    exact hone.inv.of_formEq hL (fun U _ h => by simp [Fin.prod_univ_succ])
  | one =>
    exact (hone.mul hone.inv).of_formEq hL (fun U _ h => by
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type])
  | more n ih₀ ih₁ =>
    refine ((hcube.pull (lift (x ^ (n + 1)) (lift x x⁻¹)).left).mul
      ((ih₁.mul ih₁).mul (ih₀.inv.mul ((hone.mul hone).mul hsym)))).of_formEq hL (fun U _ h => ?_)
    refine ((Fintype.prod_sum_type _).trans
      (congrArg₂ (· * ·) (prod_cub (x ^ (n + 1)) x x⁻¹ h) rfl)).trans ?_
    have e₁ : x ^ (n + 1) * x * x⁻¹ = x ^ (n + 1) := mul_inv_cancel_right _ _
    have e₂ : x ^ (n + 1) * x = x ^ (n + 2) := (pow_succ x (n + 1)).symm
    have e₃ : x ^ (n + 1) * x⁻¹ = x ^ n := by rw [pow_succ, mul_inv_cancel_right]
    rw [e₁, e₂, e₃, mul_inv_cancel]
    apply Additive.ofMul.injective
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
    push_cast
    module

theorem mulPull_of_cube_of_symm :
    (∀ (S : Scheme.{0}) (P : PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) →
    (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S), ∃ nu : LB.Gen (negLB P.A P.L k T), nu.IsGen) →
    (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2)
      ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) ∧ MulPullSt := by
  intro hc hs
  have main : ∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2)
      ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen := by
    intro S P n
    have hcube : HasGen P.L (thφ P.A (x3 P.A)) thε := hc S P P.L P.isLB
    have hrig : HasGen P.L (K := PUnit) (fun _ => eSec P.A) (fun _ => 1) := P.rigid
    have hneg : HasGen P.L (K := Fin 2) ![(snd P.A P.A).left,
      (snd P.A P.A ≫ (GrpObj.inv : P.A ⟶ P.A)).left] ![1, -1] := hs S P 1 P.A
    refine hasGen_pow P.isLB hcube (𝟙 P.A) ?_ ?_ n
    · refine (hrig.pull (toUnit P.A).left).of_formEq P.isLB (fun U _ h => ?_)
      simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, _root_.mul_one]
      rfl
    · refine (hneg.pull (lift (𝟙 P.A) (𝟙 P.A)).left).of_formEq P.isLB (fun U _ h => ?_)
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        ← Over.comp_left, lift_snd, lift_snd_assoc]
      rfl
  exact ⟨main, fun S _ P n => main S P n⟩

end GlobalTheory.MulPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecDivOfThickenings
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ThickeningDivisible

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Cartier EffCartierData TopologicalSpace
open ThickeningDetermines ThickeningClosed

theorem gs_zero {X Z : Scheme.{0}} (q : Z ⟶ X) (z : Z) (U : X.Opens) : gs q z U 0 = 0 := by
  unfold gs
  split_ifs
  · rw [map_zero, map_zero]
  · rfl

theorem cst_comp_eq_zero {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {r : R}
    (hr : φ r = 0) {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R')) (z : Z) :
    cst (q ≫ Spec.map (CommRingCat.ofHom φ)) z r = 0 := by
  have h : ((Spec.map (CommRingCat.ofHom φ)).app ⊤).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = 0 := by
    have := congrArg (fun k ↦ k.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [hr, map_zero] at this
    exact this.symm
  rw [cst, ← gs_pull q _ z ⊤ trivial, h, gs_zero]

theorem constFn_dvd_of_mem_ker {R : Type} [CommRing R] {X Z : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) (r : R) (i : Z ⟶ X)
    (l : pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r})))) ⟶ Z)
    (hl : l ≫ i = pullback.fst _ _) {W : X.Opens} (hW : IsAffineOpen W) {a : Γ(X, W)}
    (ha : a ∈ i.ker.ideal ⟨W, hW⟩) : constFn p W r ∣ a := by
  let φ : CommRingCat.of R ⟶ Γ(X, W) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ W le_top
  have hφ : Spec.map φ = hW.fromSpec ≫ p := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hW le_top
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [← h, Spec.map_comp]
  have := ker_ideal_le_ker i hW
    (CommRingCat.ofHom (Ideal.Quotient.mk ((Ideal.span {r}).map φ.hom)))
    (pullback.lift (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((Ideal.span {r}).map φ.hom))) ≫
      hW.fromSpec)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((Ideal.span {r}).map φ.hom) φ.hom
        Ideal.le_comap_map)))
      (by
        rw [Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_comp]
        rfl) ≫ l)
    (by rw [Category.assoc, hl, pullback.lift_fst]) ha
  rw [CommRingCat.hom_ofHom, Ideal.mk_ker, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at this
  exact this

theorem map_le_jacobson {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (hφ : Function.Surjective φ) {I : Ideal R} (hI : I ≤ Ideal.jacobson ⊥) :
    I.map φ ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_jacobson_of_surjective hφ]
  exact hI.trans (Ideal.jacobson_mono bot_le)

end ThickeningDivisible


end GlobalTheory
end

