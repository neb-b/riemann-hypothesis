module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1925
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1900
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoDetConormalProd
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HodgeProd

open GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.Twist (resM resM_resM app_resM)

section Split

variable {S : Scheme.{0}} {F F₁ F₂ : S.Modules} {p₁ : F₁ ⟶ F} {p₂ : F₂ ⟶ F} {i₁ : F ⟶ F₁}
    {i₂ : F ⟶ F₂} (h : i₁ ≫ p₁ + i₂ ≫ p₂ = 𝟙 _) (h₁ : p₁ ≫ i₁ = 𝟙 _) (h₂ : p₂ ≫ i₂ = 𝟙 _) (h₃ : p₁ ≫ i₂ = 0)
    (h₄ : p₂ ≫ i₁ = 0) {U V : S.Opens} {n m : ℕ} {e₁ : Fin n → Γ(F₁, U)} {e₂ : Fin m → Γ(F₂, U)}
    (he₁ : VB.IsFrame e₁) (he₂ : VB.IsFrame e₂)


include h h₁ h₂ h₃ h₄ in
theorem repr_left (hV : V ≤ U) (y : Γ(F, V)) (i : Fin n) :
    ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr y (Fin.castAdd m i) =
      (he₁.basis hV).repr (i₁.app V y) i := by
  have key : (Finsupp.lapply (Fin.castAdd m i)).comp
      ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr.toLinearMap =
      (Finsupp.lapply i).comp ((he₁.basis hV).repr.toLinearMap.comp (QCoh.appLinear i₁ V)) := by
    refine ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).ext fun k => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_left, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₁]
      change _ = ((he₁.basis hV).repr ((resM F₁ hV) (e₁ j))) i
      rw [← IsFrame.basis_apply he₁ hV, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
      simp [Fin.castAdd_inj]
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_right, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₄]
      change _ = ((he₁.basis hV).repr 0) i
      rw [map_zero, Finsupp.single_apply]
      simp only [Finsupp.coe_zero, Pi.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
  exact LinearMap.congr_fun key y


include h h₁ h₂ h₃ h₄ in
theorem repr_right (hV : V ≤ U) (y : Γ(F, V)) (i : Fin m) :
    ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr y (Fin.natAdd n i) =
      (he₂.basis hV).repr (i₂.app V y) i := by
  have key : (Finsupp.lapply (Fin.natAdd n i)).comp
      ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr.toLinearMap =
      (Finsupp.lapply i).comp ((he₂.basis hV).repr.toLinearMap.comp (QCoh.appLinear i₂ V)) := by
    refine ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).ext fun k => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_left, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₃]
      change _ = ((he₂.basis hV).repr 0) i
      rw [map_zero, Finsupp.single_apply]
      simp only [Finsupp.coe_zero, Pi.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_right, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₂]
      change _ = ((he₂.basis hV).repr ((resM F₂ hV) (e₂ j))) i
      rw [← IsFrame.basis_apply he₂ hV, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
      simp [Fin.natAdd_inj]
  exact LinearMap.congr_fun key y


include h h₁ h₂ h₃ h₄ in
theorem detUnit_append {U' : S.Opens} {e₁' : Fin n → Γ(F₁, U')} {e₂' : Fin m → Γ(F₂, U')}
    (he₁' : VB.IsFrame e₁') (he₂' : VB.IsFrame e₂') (hV : V ≤ U) (hV' : V ≤ U') :
    (GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).detUnit
                 (GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁' he₂') hV hV' =
      he₁.detUnit he₁' hV hV' * he₂.detUnit he₂' hV hV' := by
  refine Units.ext ?_
  rw [Units.val_mul, IsFrame.val_detUnit, IsFrame.val_detUnit, IsFrame.val_detUnit, Module.Basis.det_apply,
    Module.Basis.det_apply, Module.Basis.det_apply]
  have hM : ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).toMatrix
      (fun k => resM F hV' (Fin.append (fun i => p₁.app U' (e₁' i)) (fun j => p₂.app U' (e₂' j)) k)) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks
        ((he₁.basis hV).toMatrix fun i => resM F₁ hV' (e₁' i)) 0 0
        ((he₂.basis hV).toMatrix fun i => resM F₂ hV' (e₂' i))) := by
    ext k l
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) l
    all_goals
      simp only [Module.Basis.toMatrix_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Fin.append_left,
        Fin.append_right, Matrix.zero_apply]
    · rw [repr_left h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₁]; rfl
    · rw [repr_left h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₄]
      change ((he₁.basis hV).repr 0) i = 0
      simp
    · rw [repr_right h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₃]
      change ((he₂.basis hV).repr 0) i = 0
      simp
    · rw [repr_right h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₂]; rfl
  rw [hM, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

end Split

section Prod

open GlobalTheory.Conormal

variable {S : Scheme.{0}} (G H : Over S) [GrpObj G] [GrpObj H]

theorem lbIso_det_conormal_prod [QuasiSeparated G.hom] [QuasiSeparated H.hom] (g h : ℕ)
    (hG : IsVB (omega G) g) (hH : IsVB (omega H) h) (t : 𝟙_ (Over S) ⟶ G ⊗ H) (ht : t = lift η[G] η[H]) :
    LBIso (VB.det (conormal (sec t)) (g + h)) (CechPic.tens (VB.det (omega G) g) (VB.det (omega H) h)) := by
  subst ht
  have i₁ : η[G] ≫ lift (𝟙 G) (toUnit G ≫ η[H]) = lift η[G] η[H] := by simp
  have i₂ : η[H] ≫ lift (toUnit H ≫ η[G]) (𝟙 H) = lift η[G] η[H] := by simp
  have p₁ := lift_fst η[G] η[H]
  have p₂ := lift_snd η[G] η[H]
  have c₁ : η[H] ≫ toUnit H ≫ η[G] = η[G] := by simp
  have c₂ : η[G] ≫ toUnit G ≫ η[H] = η[H] := by simp
  have H₀ := cotMap_prod i₁ i₂ p₁ p₂
  have H₁ := (cotMap_comp p₁ i₁ (lift_fst _ _) (Category.comp_id _)).trans (cotMap_id rfl _)
  have H₂ := (cotMap_comp p₂ i₂ (lift_snd _ _) (Category.comp_id _)).trans (cotMap_id rfl _)
  have H₃ := (cotMap_comp p₁ i₂ (lift_fst _ _) c₁).trans (cotMap_eq_zero rfl _)
  have H₄ := (cotMap_comp p₂ i₁ (lift_snd _ _) c₂).trans (cotMap_eq_zero rfl _)
  let L := CechPic.tens (VB.det (omega G) g) (VB.det (omega H) h)
  have hL : L.IsLB := CechPic.isLB_tens hG.isLB_det hH.isLB_det
  have he : ∀ p : L.ι, IsFrame (Fin.append
      (fun i => (cotMap (fst G H) p₁).app (L.U p) (resM (omega G) inf_le_left (p.1.e i)))
      (fun j => (cotMap (snd G H) p₂).app (L.U p) (resM (omega H) inf_le_right (p.2.e j)))) := fun p =>
    GlobalTheory.TorusCot.isFrame_append H₀ H₁ H₂ H₃ H₄ (p.1.isFrame.res inf_le_left) (p.2.isFrame.res inf_le_right)
  refine LBIso.symm (lbIso_det_of_frames hL _ he fun p q => ?_).2
  refine Eq.trans ?_ (detUnit_append H₀ H₁ H₂ H₃ H₄ (p.1.isFrame.res inf_le_left) (p.2.isFrame.res inf_le_right)
    (q.1.isFrame.res inf_le_left) (q.2.isFrame.res inf_le_right) inf_le_left inf_le_right).symm
  exact congrArg₂ (· * ·) ((IsFrame.res_detUnit _ _ _ _ _).trans (IsFrame.detUnit_res _ _ _ _ _ _).symm)
    ((IsFrame.res_detUnit _ _ _ _ _).trans (IsFrame.detUnit_res _ _ _ _ _ _).symm)

end Prod

end GlobalTheory.HodgeProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelAutomorphismUnipotentFixesComplexPointEqOne
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.UnipFree

theorem free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ «γ» : LevelAut Dw l, UnipAt I «γ» → ∀ y : FrPt Xo c ℂ, ptF (move Xo c «γ» y) = ptF y → «γ» = 1 := by
  intro E _ _ _ H Dw l Xo c hpq hA1 I g hN hMb «γ» hU y hy
  have hA : l.A.Coprime l.M := by rw [hA1]; exact Nat.coprime_one_left _
  obtain ⟨ρ, ν, hiso, hm, hf⟩ := GlobalTheory.LevDesc.levR_move (Xo := Xo) (c := c) hpq hA «γ» y
  have hm' : IsLevMove ρ ν (liftLa «γ») LinearMap.id := hm
  have hx : y.x ≫ ρ = y.x := by
    have e := congrArg (· ≫ pullback.fst _ _) hy
    simp only [GlobalTheory.AllWt.ptF, pullback.lift_fst] at e
    rw [← hf.1]; exact e
  obtain ⟨hg, hnorm, hsq, hr⟩ := hN
  set x := y.x with hxdef
  set G := Xo.univ.t.G with hGdef
  let G0 : Over (Sp ℂ) := (Over.pullback x).obj G
  let act0 : OAct (𝓞 E) G0 := OAct.pullback x G Xo.univ.t.act
  have w : (pullback.fst G.hom x ≫ ν.φ) ≫ G.hom = pullback.snd G.hom x ≫ x := by
    rw [Category.assoc, ν.cart.1.w, ← Category.assoc, pullback.condition, Category.assoc, hx]
  let α : G0 ⟶ G0 := Over.homMk (pullback.lift (pullback.fst G.hom x ≫ ν.φ) (pullback.snd G.hom x) w)
    (pullback.lift_snd _ _ _)
  have hαf : α.left ≫ pullback.fst G.hom x = pullback.fst G.hom x ≫ ν.φ := pullback.lift_fst _ _ _
  have pA : IsGrpPullback G0 G x (pullback.fst G.hom x) := isGrpPullback_pullback G x
  have c₁ : IsGrpPullback G0 G x (pullback.fst G.hom x ≫ ν.φ) := by
    have c₀ := IsGrpPullback.comp pA ν.cart
    rw [hx] at c₀
    exact c₀
  have hαm : IsMonHom α :=
    ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback c₁ pA (𝟙 G) α (by simpa using hαf)
  have hact0 : ∀ a, (act0.act a).left ≫ pullback.fst G.hom x = pullback.fst G.hom x ≫ (Xo.univ.t.act.act a).left :=
    fun a => pullback.lift_fst _ _ _
  have hact : ∀ a, act0.act a ≫ α = α ≫ act0.act a := fun a => by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · calc (act0.act a ≫ α).left ≫ pullback.fst G.hom x
          = (act0.act a).left ≫ (α.left ≫ pullback.fst G.hom x) := by rw [Over.comp_left, Category.assoc]
        _ = ((act0.act a).left ≫ pullback.fst G.hom x) ≫ ν.φ := by rw [hαf, Category.assoc]
        _ = pullback.fst G.hom x ≫ ((Xo.univ.t.act.act a).left ≫ ν.φ) := by rw [hact0, Category.assoc]
        _ = pullback.fst G.hom x ≫ (ν.φ ≫ (Xo.univ.t.act.act a).left) :=
          congrArg (pullback.fst G.hom x ≫ ·) (ν.act a)
        _ = (α.left ≫ pullback.fst G.hom x) ≫ (Xo.univ.t.act.act a).left := by rw [hαf, Category.assoc]
        _ = α.left ≫ ((act0.act a).left ≫ pullback.fst G.hom x) := by rw [hact0, Category.assoc]
        _ = (α ≫ act0.act a).left ≫ pullback.fst G.hom x := by rw [Over.comp_left, Category.assoc]
    · have h1 : ∀ f : G0 ⟶ G0, f.left ≫ pullback.snd G.hom x = pullback.snd G.hom x := fun f => Over.w f
      simp only [Over.comp_left, Category.assoc, h1]
  obtain ⟨n, hn, hνn⟩ := _root_.GlobalTheory.MoveOrder.finite_order E H Dw l Xo c «γ» ρ ν hpq hA1 hiso hm'
  have hαn : (fun f => f ≫ α)^[n] (𝟙 G0) = 𝟙 G0 := by
    have key : ∀ j, ((fun f => f ≫ α)^[j] (𝟙 G0)).left ≫ pullback.fst G.hom x =
        pullback.fst G.hom x ≫ (fun f : G.left ⟶ G.left => f ≫ ν.φ)^[j] (𝟙 _) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Over.comp_left, Category.assoc, hαf,
          ← Category.assoc, ih, Category.assoc]
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [key, hνn, Over.id_left, Category.id_comp, Category.comp_id]
    · have h1 : ∀ f : G0 ⟶ G0, f.left ≫ pullback.snd G.hom x = pullback.snd G.hom x := fun f => Over.w f
      rw [h1]; simp

  have bw : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (u.left ≫ pullback.fst G.hom x) ≫ G.hom = (Over.mk x).hom := fun u => by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have e : u.left ≫ pullback.snd G.hom x = 𝟙 _ := Over.w u
    rw [e, Category.id_comp]; rfl
  let B : (𝟙_ (Over (Sp ℂ)) ⟶ G0) → (Over.mk x ⟶ G) := fun u => Over.homMk (u.left ≫ pullback.fst G.hom x) (bw u)
  have B_left : ∀ u, (B u).left = u.left ≫ pullback.fst G.hom x := fun u => rfl
  have B_inj : Function.Injective B := fun u v h => by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congrArg (fun z => z.left) h
    · exact (Over.w u).trans (Over.w v).symm
  have B_mul : ∀ u v, B (u * v) = B u * B v := fun u v => by
    apply Over.OverMorphism.ext
    have e1 := pA.2 (𝟙_ _) u v (pushPt pA.1.w u) (pushPt pA.1.w v) rfl rfl
    have e2 := mul_left_congr (Category.id_comp x) (pushPt pA.1.w u) (pushPt pA.1.w v) (B u) (B v) rfl rfl
    exact e1.symm.trans e2
  let Bh : (𝟙_ (Over (Sp ℂ)) ⟶ G0) →* (Over.mk x ⟶ G) := MonoidHom.mk' B B_mul
  have B_act : ∀ u a, B (u ≫ act0.act a) = B u ≫ Xo.univ.t.act.act a := fun u a => by
    apply Over.OverMorphism.ext
    rw [B_left, Over.comp_left, Over.comp_left, B_left, Category.assoc, Category.assoc, hact0]
  have B_α : ∀ u, (B (u ≫ α)).left = (B u).left ≫ ν.φ := fun u => by
    rw [B_left, B_left, Over.comp_left, Category.assoc, hαf, Category.assoc]
  have B_one : B 1 = 1 := map_one Bh

  have tl : (toUnit (Over.mk x)).left = x := by simpa using Over.w (toUnit (Over.mk x))
  let β : KA l →+* ℂ := (algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom
  obtain ⟨-, TI, -, -, hTI⟩ := Xo.univ.geom ℂ x β y.x_over
  let et : Dw.La → (Over.mk x ⟶ G) := fun b => toUnit (Over.mk x) ≫ Xo.univ.eta b
  have et_add : ∀ a b, et (a + b) = et a * et b := fun a b => by
    simp only [et, Xo.univ.eta_add, MonObj.comp_mul]
  have et_ker : ∀ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La), et a = 1 := fun a ha => by
    simp only [et, Xo.univ.eta_ker a ha, MonObj.comp_one]
  have hadd : ∀ (a b : 𝓞 E) (z : Over.mk x ⟶ G), z ≫ Xo.univ.t.act.act (a + b) =
      (z ≫ Xo.univ.t.act.act a) * (z ≫ Xo.univ.t.act.act b) := fun a b z => by
    rw [Xo.univ.t.act.add, MonObj.comp_mul]
  have hone : ∀ z : Over.mk x ⟶ G, z ≫ Xo.univ.t.act.act 1 = z := fun z => by
    rw [Xo.univ.t.act.one, Category.comp_id]
  have hnat : ∀ (k : ℕ) (z : Over.mk x ⟶ G), z ≫ Xo.univ.t.act.act (k : 𝓞 E) = z ^ k := by
    intro k z
    induction k with
    | zero =>
      have h0 := hadd 0 0 z
      rw [add_zero] at h0
      simpa using h0
    | succ k ih => rw [Nat.cast_succ, hadd, ih, hone, pow_succ]
  obtain ⟨t, ht, htor⟩ := _root_.GlobalTheory.TateTorsion.torsion_eq_level_smul E H Dw l ℂ (Over.mk x ⟶ G) (fun a z => z ≫ Xo.univ.t.act.act a) _ TI et I g
    hadd hone hnat (fun a ha => hTI a ha) hg hnorm hsq hMb

  have tor_B : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (∀ a ∈ I, u ≫ act0.act a = 1) → ∃ c' : Dw.La, B u = et (t • c') :=
    fun u hu => htor (B u) fun a ha => by rw [← B_act, hu a ha, B_one]
  obtain ⟨hfin, hcard⟩ := _root_.GlobalTheory.natCard_quot_smul_top_le_pow_finrank E Dw.La Dw.fin Dw.proj I g hg hnorm
  classical
  haveI : Fintype (Dw.La ⧸ I • (⊤ : Submodule (𝓞 E) Dw.La)) := Fintype.ofFinite _
  let rep := Function.surjInv (Submodule.Quotient.mk_surjective (I • (⊤ : Submodule (𝓞 E) Dw.La)))
  let S' : Finset (Over.mk x ⟶ G) := Finset.univ.image fun q => et (t • rep q)
  have et_t : ∀ c', et (t • c') ∈ S' := fun c' => by
    refine Finset.mem_image.2 ⟨Submodule.Quotient.mk c', Finset.mem_univ _, ?_⟩
    have e : rep (Submodule.Quotient.mk c') - c' ∈ I • (⊤ : Submodule (𝓞 E) Dw.La) :=
      (Submodule.Quotient.eq _).1 (Function.surjInv_eq _ _)
    have e2 := ht _ e
    rw [smul_sub] at e2
    have e3 : et (t • rep (Submodule.Quotient.mk c')) =
        et (t • rep (Submodule.Quotient.mk c') - t • c') * et (t • c') := by
      rw [← et_add, sub_add_cancel]
    rw [e3, et_ker _ e2, _root_.one_mul]
  let T0 : Finset (𝟙_ (Over (Sp ℂ)) ⟶ G0) := S'.preimage B B_inj.injOn
  have hT0 : T0.card ≤ g ^ (Dw.p + Dw.q) := by
    calc T0.card ≤ S'.card :=
          Finset.card_le_card_of_injOn B (fun u hu => Finset.mem_preimage.1 hu) B_inj.injOn
      _ ≤ (Finset.univ : Finset (Dw.La ⧸ I • (⊤ : Submodule (𝓞 E) Dw.La))).card := Finset.card_image_le
      _ = Nat.card (Dw.La ⧸ I • (⊤ : Submodule (𝓞 E) Dw.La)) := by
          rw [Finset.card_univ, Nat.card_eq_fintype_card]
      _ ≤ g ^ (Dw.p + Dw.q) := by rw [← Dw.rank]; exact hcard
  have hmemT : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (∀ a ∈ I, u ≫ act0.act a = 1) → u ∈ T0 := fun u hu => by
    obtain ⟨c', hc'⟩ := tor_B u hu
    exact Finset.mem_preimage.2 (hc' ▸ et_t c')

  obtain ⟨m, hmU⟩ := _root_.GlobalTheory.OrbitSep.unipAt_inv_liftLa E H Dw l I «γ» hMb hU
  have hδ : ∀ b, et (liftLa «γ» (liftLa «γ»⁻¹ b)) = et b := fun b => by
    have e1 := GlobalTheory.LevelActionLaws.liftLa_mul_sub «γ» «γ»⁻¹ b
    have e2 := GlobalTheory.LevelActionLaws.liftLa_one_sub (D := Dw) (l := l) b
    rw [mul_inv_cancel] at e1
    have e3 : liftLa «γ» (liftLa «γ»⁻¹ b) - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
      have e4 := Submodule.sub_mem _ e2 e1
      rwa [sub_sub_sub_cancel_left] at e4
    have e5 : et (liftLa «γ» (liftLa «γ»⁻¹ b)) = et (liftLa «γ» (liftLa «γ»⁻¹ b) - b) * et b := by
      rw [← et_add, sub_add_cancel]
    rw [e5, et_ker _ e3, _root_.one_mul]
  have B_step : ∀ u b, B u = et b → B (u ≫ α) = et (liftLa «γ»⁻¹ b) := fun u b hb => by
    apply Over.OverMorphism.ext
    rw [B_α, hb, ← hδ b]
    show (toUnit (Over.mk x) ≫ Xo.univ.eta (liftLa «γ» (liftLa «γ»⁻¹ b))).left ≫ ν.φ =
      (toUnit (Over.mk x) ≫ Xo.univ.eta (liftLa «γ»⁻¹ b)).left
    rw [Over.comp_left, Over.comp_left, Category.assoc, hm'.2.1, tl, ← Category.assoc, hx]
  let φf : (𝟙_ (Over (Sp ℂ)) ⟶ G0) → (𝟙_ (Over (Sp ℂ)) ⟶ G0) := fun z => (z ≫ α) * z⁻¹
  have B_iter : ∀ j u b, B u = et b → B (φf^[j] u) = et (((liftLa «γ»⁻¹ - 1) ^ j) b) := by
    intro j
    induction j with
    | zero => intro u b hb; simpa using hb
    | succ j ih =>
      intro u b hb
      rw [Function.iterate_succ_apply']
      have h1 := ih u b hb
      set b' := ((liftLa «γ»⁻¹ - 1) ^ j) b
      show Bh ((φf^[j] u ≫ α) * (φf^[j] u)⁻¹) = _
      rw [map_mul, map_inv]
      show B (φf^[j] u ≫ α) * (B (φf^[j] u))⁻¹ = _
      rw [B_step _ _ h1, h1, pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
      rw [eq_comm, eq_mul_inv_iff_mul_eq, ← et_add, sub_add_cancel]
  have hunip : ∀ u : 𝟙_ (Over (Sp ℂ)) ⟶ G0, (∀ a ∈ I, u ≫ act0.act a = 1) →
      (fun z : 𝟙_ (Over (Sp ℂ)) ⟶ G0 => (z ≫ α) * z⁻¹)^[m] u = 1 := fun u hu => by
    obtain ⟨c', hc'⟩ := tor_B u hu
    apply B_inj
    rw [B_iter m u _ hc', B_one, map_smul]
    exact et_ker _ (ht _ (hmU c'))
  have hαid : α = 𝟙 G0 := _root_.GlobalTheory.NeatUnip.finite_order_unipotent_eq_id E ℂ G0 act0 α n m g (Dw.p + Dw.q) I
    (IsSemiAbelian.pullback x G Xo.univ.t.semi) hαm hact hn hαn hg hnorm hsq hr ⟨T0, hT0, hmemT⟩ hunip

  have hαl : α.left = 𝟙 _ := by rw [hαid]; rfl
  have fix : ∀ s : Over.mk x ⟶ G, s.left ≫ ν.φ = s.left := fun s => by
    have hs : s.left ≫ G.hom = 𝟙 (Sp ℂ) ≫ x := by rw [Category.id_comp]; exact Over.w s
    have e0 : pullback.lift s.left (𝟙 _) hs ≫ pullback.fst G.hom x = s.left := pullback.lift_fst _ _ _
    rw [← e0, Category.assoc, ← hαf, hαl, Category.id_comp]
  have heq : ∀ a, liftLa «γ» a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := fun a => by
    refine GlobalTheory.LevelFree.eta_injective Xo x β y.x_over _ ?_
    have e1 : et (liftLa «γ» a) = et a := by
      apply Over.OverMorphism.ext
      rw [← fix (et (liftLa «γ» a))]
      show (toUnit (Over.mk x) ≫ Xo.univ.eta (liftLa «γ» a)).left ≫ ν.φ =
        (toUnit (Over.mk x) ≫ Xo.univ.eta a).left
      rw [Over.comp_left, Over.comp_left, Category.assoc, hm'.2.1, tl, ← Category.assoc, hx]
    have e2 : et (liftLa «γ» a) = et (liftLa «γ» a - a) * et a := by rw [← et_add, sub_add_cancel]
    rw [e1] at e2
    exact mul_eq_right.1 e2.symm
  refine LinearEquiv.ext fun q => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have e := liftLa_spec «γ» a
  simp only [Submodule.mkQ_apply] at e
  change «γ» (Submodule.Quotient.mk a) = Submodule.Quotient.mk a
  rw [← e]
  exact (Submodule.Quotient.eq _).2 (heq a)

end GlobalTheory.UnipFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisCardEqDimUniformisationDvr
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieRankUnif

theorem card_eq_g : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (IsLocalRing.maximalIdeal V) D A G) (n : ℕ) (y : Fin n → (epsR V ⟶ G)), IsLieBasis y → n = A.g := by
  intro V _ _ _ D A G _ _ U n y hy
  have := U.smooth
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  obtain ⟨φ, gp⟩ : ∃ φ : A.A.left ⟶ G.left, IsGrpPullback A.A G (jK V) φ :=
    ⟨_, ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK V))).congr (Category.id_comp _) rfl⟩
  obtain ⟨v, hv, -⟩ := GlobalTheory.exists_isLieBasis_baseChange V (FractionRing V) (algebraMap V _) G A.A φ gp U.smooth n y hy
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.KeyPow.exists_isLieBasis A.A A.smoothDim
  exact GlobalTheory.KeyFramePoint.card_eq_of_isLieBasis gp hv hv₀

end GlobalTheory.LieRankUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactEquivarianceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_compact_equivariance : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ W.J → ℂ, (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val)) →
    ∀ (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
      (∀ (g : UA σ W.J) (gd : GlobalTheory.DblScal.UD σ W.J),
        ((gd : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
          Matrix.fromBlocks (mat g) 0 0 1 →
        ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), omd gd (boxFun φ₁ φ₂) = boxFun (om (1, g) φ₁) φ₂) →
      GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd →
      (∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
        ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) *
          starRingEnd ℂ (ι (fun x => starRingEnd ℂ (φ₂ x)) (Y.submatrix id Sum.inr))) →
      ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∀ h ∈ UAt σ W (evFin F v), ∀ gd : GlobalTheory.DblScal.UD σ W.J,
        ((gd : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
          Matrix.fromBlocks (mat h) 0 0 1 → κ h = cd gd := by
  first | exact @GlobalTheory.DblScalBox.scal_diag_one | exact GlobalTheory.DblScalBox.scal_diag_one | (intros; apply GlobalTheory.DblScalBox.scal_diag_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelDoubleSplittingStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_double_splitting : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ dd : GlobalTheory.DblScal.DblCo σ X W, IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
    ∃ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd ∧
      ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
        ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) *
          starRingEnd ℂ (ι (fun x => starRingEnd ℂ (φ₂ x)) (Y.submatrix id Sum.inr)) := by
  first | exact @GlobalTheory.DblLin.dblLin | exact GlobalTheory.DblLin.dblLin | (intros; apply GlobalTheory.DblLin.dblLin <;> assumption)
end

