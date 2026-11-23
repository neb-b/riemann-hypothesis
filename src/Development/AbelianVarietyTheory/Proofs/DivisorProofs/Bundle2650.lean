module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2604
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2601
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2479
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisExtendsNormalAffineC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupExtendsNormalAffineChartAfterRescaling
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2600

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrBoxOfIsSumDeg
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.SumDeg

variable {R : Type} [CommRing R] [IsDomain R] {D D₁ D₂ : DegPre R} (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A)
  [IsMonHom p₁] [IsMonHom p₂] (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left))

theorem isBoxGen_cub (hw : w.IsGen) :
    IsBoxGen w (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left D.cub.t D₁.cub.t D₂.cub.t := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D.P.A := lift 1 (lift 1 1)
  have sj : Function.Surjective
      ((snd D.P.A (D.P.A ⊗ D.P.A)).left ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D.P.isAb _) (surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2)
  have he : e.left ≫ (snd D.P.A (D.P.A ⊗ D.P.A)).left ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  refine isBoxGen_of_section w hw D₁.P.isLB D₂.P.isLB D.P.isLB (ε := thε)
    (fun a => (CubeMap.ofHom p₁).psum_comm a.down) (fun a => (CubeMap.ofHom p₂).psum_comm a.down)
    D.cub.isGen D₁.cub.isGen D₂.cub.isGen _ e.left he sj fun s I₁ I₂ I hI₁ hI₂ hI => ?_
  have C : IsCub (cubV D.cub s I) := isCub_cubV D.cub hI
  have C₁ : IsCub (cubV D₁.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) s I₁) := isCub_cubV D₁.cub hI₁
  have C₂ : IsCub (cubV D₂.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) s I₂) := isCub_cubV D₂.cub hI₂
  have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) 1 1 (om w s I₁ I₂ I)
  rw [_root_.mul_one, _root_.mul_one] at p
  have o₁ : e.left ≫ (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left =
      (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D₁.P.A) (lift 1 1)).left := by
    refine (groupObj_lift3_comp_tensorCube_monHom p₁ 1 1 1).trans ?_
    rw [MonObj.one_comp]
  have o₂ : e.left ≫ (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left =
      (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D₂.P.A) (lift 1 1)).left := by
    refine (groupObj_lift3_comp_tensorCube_monHom p₂ 1 1 1).trans ?_
    rw [MonObj.one_comp]
  have v₁ := (congrArg (fun m => val D₁.cub.t m s I₁) o₁).trans (C₁.face 1 1)
  have v₂ := (congrArg (fun m => val D₂.cub.t m s I₂) o₂).trans (C₂.face 1 1)
  exact (congrArg₂ (· * ·) p (C.face 1 1)).trans (Eq.trans (by simp) (congrArg₂ (· * ·) v₁ v₂).symm)

theorem isBoxGen_sym (hw : w.IsGen) : IsBoxGen w p₁.left p₂.left D.sym D₁.sym D₂.sym := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  refine isBoxGen_of_section w hw D₁.P.isLB D₂.P.isLB D.P.isLB (inv_comp p₁) (inv_comp p₂)
    D.sym_gen D₁.sym_gen D₂.sym_gen D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2
    fun s I₁ I₂ I hI₁ hI₂ hI => ?_
  have q := prod_sym (eSec D.P.A) (om w s I₁ I₂ I)
  have o : eSec D.P.A ≫ (ι[D.P.A]).left = eSec D.P.A :=
    congrArg (fun m => m.left) (GrpObj.one_inv : η[D.P.A] ≫ ι[D.P.A] = η[D.P.A])
  rw [o, mul_inv_cancel] at q
  rw [eSec_comp, eSec_comp, val_sym_zero D₁ hI₁, val_sym_zero D₂ hI₂]
  exact congrArg₂ (· * ·) q (val_sym_zero D hI)

theorem exists_strBox_of_isSumDeg : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∃ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)), StrBox p₁ p₂ w D.rig D₁.rig D₂.rig D.cub.t D₁.cub.t D₂.cub.t D.sym D₁.sym D₂.sym ∧ ∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x)) := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ h
  have := h.hom₁
  have := h.hom₂
  obtain ⟨w, hw, hr, hψ⟩ := h.w
  exact ⟨w, ⟨hw, isBoxGen_of_mapsAt w _ _ hr, isBoxGen_cub p₁ p₂ w hw, isBoxGen_sym p₁ p₂ w hw⟩,
    fun x => isBoxGen_of_mapsAt w _ _ (hψ x)⟩

end GlobalTheory.ProdUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTheoremOfSquareSemiAbelianGenericAbelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SquareGeneric

theorem exists_gen_square :
    ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSemiAbelian G' → IsAbelianScheme ((Over.pullback (jK R')).obj G') → ∀ N : LB G'.left, N.IsLB → ∀ a : 𝟙_ (Over (Sp R')) ⟶ G', ∃ t : LB.Gen (LB.LinComb N (K := Fin 3) ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left] ![1, 1, -2]), t.IsGen := by
  intro R' _ _ _ _ _ G' _ hG hA N hN a
  have := hG.comm
  let j := jK R'
  let πA := pullback.fst G'.hom j
  have hp : IsProper (pullback.snd G'.hom j) := hA.proper
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.RigCube.exists_gen_theta_generic G' hG hp hN
  let c : G' ⟶ G' := toUnit G' ≫ a
  let c' : G' ⟶ G' := toUnit G' ≫ a⁻¹
  let ℓ : G' ⟶ G3 G' := lift (𝟙 G') (lift c c')
  let h : pullback G'.hom j ⟶ pullback (G3 G').hom j :=
    pullback.map _ _ _ _ ℓ.left (𝟙 _) (𝟙 _) (by rw [Category.comp_id, Over.w]) (by simp)
  have hh : h ≫ pullback.fst (G3 G').hom j = πA ≫ ℓ.left := pullback.lift_fst _ _ _
  let t₁ := LB.pullGen (Theta G' N) (fun _ => pullback.fst (G3 G').hom j) (fun _ => 1) t₀ h
  have ht₁ : t₁.IsGen := DVR.pullGen_isGen _ _ _ _ ht₀ _
  obtain ⟨t₂, ht₂⟩ := gen_chartPull (chartPullIn N (thφ G' (x3 G')) thε (h ≫ pullback.fst (G3 G').hom j)) t₁ ht₁
  have hcc : c * c' = 1 := by
    simp only [c, c']
    rw [← MonObj.comp_mul, _root_.mul_inv_cancel, MonObj.comp_one]

  have hconst : ∀ s : 𝟙_ (Over (Sp R')) ⟶ G', ∃ i, ∀ y, (πA ≫ (toUnit G' ≫ s).left) y ∈ N.U i := by
    intro s
    obtain ⟨p₀⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R'))) := inferInstance
    obtain ⟨i, hi⟩ := exists_chart hN ((j ≫ s.left) p₀)
    have e : πA ≫ (toUnit G' ≫ s).left = pullback.snd G'.hom j ≫ j ≫ s.left := by
      have w : (toUnit G').left = G'.hom := (Category.comp_id _).symm.trans (Over.w (toUnit G'))
      rw [Over.comp_left, w, ← Category.assoc, pullback.condition, Category.assoc]
    refine ⟨i, fun y => ?_⟩
    rw [e, Scheme.Hom.comp_apply, Subsingleton.elim ((pullback.snd G'.hom j) y) p₀]
    exact hi
  let s₃ : Fin 3 → (𝟙_ (Over (Sp R')) ⟶ G') := ![a, a⁻¹, η[G']]
  choose i hi using fun k => hconst (s₃ k)
  let φw : Fin 3 → (pullback G'.hom j ⟶ G'.left) := fun k => πA ≫ (toUnit G' ≫ s₃ k).left
  obtain ⟨w, hw⟩ := GlobalTheory.AbSquare.exists_gen_of_mem_chart hN φw ![1, 1, -2] i hi
  let ψ : Fin 3 → (G'.left ⟶ G'.left) := ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left]
  have hF : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FormEq
      (Sum.elim (fun I => (h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I) φw)
      (Sum.elim (fun I => -thε I) ![1, 1, -2]) (fun k => πA ≫ ψ k) ![1, 1, -2] := by
    intro U _ g
    rw [Fintype.prod_sum_type]
    dsimp only [Sum.elim_inl, Sum.elim_inr]
    simp only [zpow_neg, Finset.prod_inv_distrib]
    have e : ∀ I, (h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I = πA ≫ (ℓ.left ≫ thφ G' (x3 G') I) :=
      fun I => by rw [hh, Category.assoc]
    have e2 : (∏ I : thK, g ((h ≫ pullback.fst (G3 G').hom j) ≫ thφ G' (x3 G') I) ^ thε I) =
        ∏ I : thK, (fun q => g (πA ≫ q)) ((lift (𝟙 G') (lift c c')).left ≫ thφ G' (x3 G') I) ^ thε I :=
      Finset.prod_congr rfl fun I _ => by rw [e I]
    rw [e2, prod_cub (𝟙 G') c c' (fun q => g (πA ≫ q))]
    rw [show 𝟙 G' * c * c' = 𝟙 G' by rw [_root_.mul_assoc, hcc, _root_.mul_one], hcc]
    have f0 : φw 0 = πA ≫ c.left := rfl
    have f1 : φw 1 = πA ≫ c'.left := rfl
    have f2 : φw 2 = πA ≫ (1 : G' ⟶ G').left := rfl
    have p0 : ψ 0 = (𝟙 G' * c).left := rfl
    have p1 : ψ 1 = (𝟙 G' * c').left := rfl
    have p2 : ψ 2 = Over.Hom.left (𝟙 G') := (Over.id_left _).symm
    rw [Fin.prod_univ_three, Fin.prod_univ_three, f0, f1, f2, p0, p1, p2]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    abel
  obtain ⟨u, hu, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN hF (LB.mulGen N _ _ _ _ (LB.invGen N _ _ t₂) w)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ ht₂) hw)
  obtain ⟨v, hv⟩ := gen_chartPull (chartPullOut N ψ ![1, 1, -2] πA (fun k => πA ≫ ψ k) (fun _ => rfl)) u hu
  exact GlobalTheory.PicGenericInj.exists_gen_of_generic R' G' hG _ (LB.isLB_linComb hN _ _) ⟨v, hv⟩

end GlobalTheory.SquareGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaFrameCubeConstantRootOfUnityStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_frame_cube_constant_root_of_unity : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ κ : X₁.S.Gam → X₁.S.Gam → X₁.S.Gam → X₁.S.R, (∀ a a' a'', κ a a' a'' ^ ((X₁.S.r * X₁.S.N) ^ 2) = 1) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) → ∀ (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))) (hρ : ρ.IsGen) (c : CubicalStr 𝔪.A.A ⟨𝔪.A.L, ρ, 𝔪.A.isLB, hρ⟩) (a a' a'' : X₁.S.Gam) (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ 𝔪.A.A.left) → 𝔪.A.L.ι), Good 𝔪.A.L z JA → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x a) (x a') (x a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr 0) (𝟙 _) z JA))).val = GlobalTheory.UT.cst (FractionRing V) z (𝔪.yK (κ a a' a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a') (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a'') (𝟙 _) z JA)).val := by
  first | exact @GlobalTheory.Poinc.CubeConst.exists_frame_cube_const | exact GlobalTheory.Poinc.CubeConst.exists_frame_cube_const | (intros; apply GlobalTheory.Poinc.CubeConst.exists_frame_cube_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaNormalisationConstantOrigin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem exists_unit_value_at_unit : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ b₀ : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b₀ → ∀ F₀ : IntFam (maximalIdeal R) D.toPre k, F₀.Lead 0 b₀ → ∃ s₀ : R, IsUnit s₀ ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (b : W) (σ : SecK C.P.L.L T.β k), T.ExpBy b σ F₀ → ∃ ε : Wˣ, ∀ J, Good C.P.L.L (cpt W) J → sval σ (unitW T.G) (cpt W) J = stalkOf (cpt W) (b * ε * T.φ s₀) * (val C.P.L.rig T.ξ (cpt W) J).val ^ k := by
  intro R _ _ _ hR D C k hk b₀ hb₀ F₀ hF₀
  obtain ⟨s₀, hs₀, h⟩ := _root_.GlobalTheory.Mum.exists_unit_origin_sum R hR D C k hk b₀ hb₀ F₀ hF₀
  refine ⟨s₀, hs₀, fun W _ _ _ T b σ hσ => ?_⟩
  obtain ⟨σ', f', hc, hp, he⟩ := hσ
  obtain ⟨ε, hε⟩ := _root_.GlobalTheory.Mum.Trait.carries_unit R D C W T k b σ' σ hc
  refine ⟨ε, fun J hJ => ?_⟩
  obtain ⟨J', hJ', -⟩ := exists_good T.U.LG.L T.U.LG.isLB (cpt W) (K := Empty) (fun e => e.elim) (fun e => e.elim)
    (fun e => e.elim) (fun e => e.elim)
  have e1 := hε J J' hJ hJ'
  rw [h W T σ' f' hp he J' hJ'] at e1
  refine mul_right_cancel₀ (pow_ne_zero k (Units.ne_zero (val T.U.LG.rig (idW W) (cpt W) J'))) ?_
  rw [e1]
  simp only [map_mul]
  ring

theorem exists_norm_const : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ b₀ : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b₀ → ∀ F₀ : IntFam (maximalIdeal R) D.toPre k, F₀.Lead 0 b₀ → ∀ s : SecK C.P.L.L C.α k, ∃ c₁ c₂ : R, c₂ ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), a ≠ 0 → b ≠ 0 → T.Exp a b s F₀ → ∃ u : Wˣ, T.φ c₂ * (u : W) * a = T.φ c₁ * b := by
  intro R _ _ _ hR D C k hk b₀ hb₀ F₀ hF₀ s
  obtain ⟨x, y, hy, h1⟩ := _root_.GlobalTheory.Mum.UnitGen.value_unit_generic R hR D C k s
  obtain ⟨s₀, hs₀, h2⟩ := exists_unit_value_at_unit R hR D C k hk b₀ hb₀ F₀ hF₀
  have key : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W), T.Exp a b s F₀ →
      ∃ ε : Wˣ, T.φ y * (b * ε * T.φ s₀) = a * T.φ x := by
    intro W _ _ _ T a b hE
    obtain ⟨σ, hσ, hgen⟩ := hE
    obtain ⟨ε, hε⟩ := h2 W T b σ hσ
    obtain ⟨J, hJ, -⟩ := exists_good C.P.L.L C.P.L.isLB (cpt W) (K := Empty) (fun e => e.elim) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim)
    have e1 := h1 W T a σ hgen J hJ
    rw [hε J hJ, ← _root_.mul_assoc, ← map_mul] at e1
    refine ⟨ε, stalkOf_injective (cpt W) (mul_right_cancel₀ ?_ e1)⟩
    exact pow_ne_zero _ (Units.ne_zero _)
  by_cases hx : x = 0
  · refine ⟨0, 1, one_ne_zero, fun W _ _ _ T a b ha hb hE => ?_⟩
    exfalso
    obtain ⟨ε, e⟩ := key W T a b hE
    rw [hx, map_zero, mul_zero] at e
    have hφy : T.φ y ≠ 0 := fun h => hy (T.inj (h.trans (map_zero _).symm))
    have hφs : T.φ s₀ ≠ 0 := (hs₀.map T.φ).ne_zero
    exact mul_ne_zero hφy (mul_ne_zero (mul_ne_zero hb (Units.ne_zero ε)) hφs) e
  · refine ⟨s₀ * y, x, hx, fun W _ _ _ T a b ha hb hE => ?_⟩
    obtain ⟨ε, e⟩ := key W T a b hE
    refine ⟨ε⁻¹, ?_⟩
    rw [map_mul]
    have hinv : (ε : W) * ((ε⁻¹ : Wˣ) : W) = 1 := Units.mul_inv ε
    linear_combination (-(((ε⁻¹ : Wˣ) : W))) * e + (T.φ y * b * T.φ s₀) * hinv

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSymmetricFunctionValuesInGroundField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.SymRat

theorem grpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem sec_eq {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}

theorem thList_congr {m : ℕ} {R : Type} [CommRing R] {x : Sp R ⟶ S} (θ : SecAt G L x) {K : Type} [Field K]
    {y y' : Sp K ⟶ S} (e : y = y') (u : Over.mk y ⟶ Over.mk x) (u' : Over.mk y' ⟶ Over.mk x) (hu : u.left = u'.left)
    {N : ℕ} {pt : Fin N → (Over.mk y ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m y (VVRank.pullS G _ u θ) pt c) :
    ∃ pt' : Fin N → (Over.mk y' ⟶ G), ThList G L ρ m y' (VVRank.pullS G _ u' θ) pt' c := by
  subst e
  obtain rfl : u = u' := Over.OverMorphism.ext hu
  exact ⟨pt, H⟩

end GlobalTheory.UMin.SymRat

namespace GlobalTheory.UMin.SymRat

theorem symAt_exists : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left)
    (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω : Type) [Field Ω] [CharZero Ω]
    (x : Sp Ω ⟶ S) (θ : SecAt G L x), Odd m → N = m ^ (4 * g) → PolFib G L g x → ∃ e : Fin N → Ω, SymAt G L ρ m x θ e := by
  intro S G _ _ L ρ hL hρ g m N Ω _ _ x θ hm hN hP
  obtain ⟨Ω', instF, instA, pt₀, c₀, hfd, hgal, -, hT, hτ⟩ := _root_.GlobalTheory.UMin.GalTh.thList_galois S G L ρ hL hρ g m N Ω x θ hm hN hP
  haveI := hfd
  haveI := hgal
  have sb := _root_.GlobalTheory.UMin.symTup_basic
  have hfix : ∀ j, ∃ e : Ω, algebraMap Ω Ω' e = symTup c₀ j := by
    intro j
    have hm : symTup c₀ j ∈ Set.range (algebraMap Ω Ω') := (IsGalois.mem_range_algebraMap_iff_fixed _).2 fun τ => by
      obtain ⟨σ, hσ⟩ := hτ τ
      have e1 : τ (symTup c₀ j) = symTup (fun b => τ (c₀ b)) j := sb.2.2.1 Ω' Ω' (τ : Ω' →+* Ω') N c₀ j
      rw [e1, show (fun b => τ (c₀ b)) = fun b => c₀ (σ b) from funext hσ, sb.2.1 Ω' N c₀ σ]
    obtain ⟨e, he⟩ := hm
    exact ⟨e, he⟩
  choose e he using hfix
  refine ⟨e, ?_⟩
  intro K _ i pt c hc j
  let k : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  letI : Algebra Ω (AlgebraicClosure K) := (k.comp i).toAlgebra
  haveI : Algebra.IsAlgebraic Ω Ω' := Algebra.IsAlgebraic.of_finite Ω Ω'
  let jj : Ω' →ₐ[Ω] AlgebraicClosure K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hcomp : (jj : Ω' →+* AlgebraicClosure K).comp (algebraMap Ω Ω') = k.comp i :=
    RingHom.ext fun r => jj.commutes r
  obtain ⟨p1, -, h1⟩ := _root_.GlobalTheory.UMin.ThPull.thList_pull S G L ρ hL hρ m N Ω' (AlgebraicClosure K) (jj : Ω' →+* AlgebraicClosure K) _ _ pt₀ c₀ hT
  obtain ⟨p2, -, h2⟩ := _root_.GlobalTheory.UMin.ThPull.thList_pull S G L ρ hL hρ m N K (AlgebraicClosure K) k _ _ pt c hc
  simp only [SecAt.pull] at h1 h2
  rw [pullS_comp G hL] at h1 h2
  have ey1 : spMap (jj : Ω' →+* AlgebraicClosure K) ≫ spMap (algebraMap Ω Ω') ≫ x = spMap (k.comp i) ≫ x := by
    rw [← Category.assoc, spMap_comp_ring, hcomp]
  have ey2 : spMap k ≫ spMap i ≫ x = spMap (k.comp i) ≫ x := by
    rw [← Category.assoc, spMap_comp_ring]
  obtain ⟨q1, H1⟩ := thList_congr θ ey1 _ (Over.homMk (spMap (k.comp i)) rfl : Over.mk (spMap (k.comp i) ≫ x) ⟶ Over.mk x)
    (by simp only [Over.comp_left, Over.homMk_left]; rw [spMap_comp_ring, hcomp]) h1
  obtain ⟨q2, H2⟩ := thList_congr θ ey2 _ (Over.homMk (spMap (k.comp i)) rfl : Over.mk (spMap (k.comp i) ≫ x) ⟶ Over.mk x)
    (by simp only [Over.comp_left, Over.homMk_left]; rw [spMap_comp_ring]) h2
  have hPy : PolFib G L g (spMap (k.comp i) ≫ x) :=
    (_root_.GlobalTheory.UMin.FibMove.polFib_move S S G L G L (𝟙 S) (𝟙 G.left) hL hL (grpPullback_self G) (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hL) g Ω
      x).2 (AlgebraicClosure K) (k.comp i) hP
  have hmAC : (m : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast (k.comp i) m]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hm.pos.ne')
  obtain ⟨σ, hσ⟩ := (_root_.GlobalTheory.UMin.ThUniq.theta_lists_unique S G L ρ hL hρ g m m N N (AlgebraicClosure K) (spMap (k.comp i) ≫ x) hm hmAC hm hmAC
    hPy).1 _ q2 q1 _ _ H2 H1
  apply k.injective
  calc k (i (e j)) = jj (algebraMap Ω Ω' (e j)) := (RingHom.congr_fun hcomp (e j)).symm
    _ = jj (symTup c₀ j) := by rw [he]
    _ = symTup (fun b => jj (c₀ b)) j := sb.2.2.1 _ _ (jj : Ω' →+* AlgebraicClosure K) _ _ _
    _ = symTup (fun b => k (c (σ b))) j := by rw [show (fun b => jj (c₀ b)) = fun b => k (c (σ b)) from funext hσ]
    _ = symTup (fun b => k (c b)) j := by rw [sb.2.1 _ N (fun b => k (c b)) σ]
    _ = k (symTup c j) := (sb.2.2.1 _ _ k _ _ _).symm

end GlobalTheory.UMin.SymRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemMovedToAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Poinc.exists_rechart_affine : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ w : X₁.M.Z, X₁.π w ∈ Set.range i → ∃ (U : X₁.M.Z.Opens) (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (fg : (X₁.M.ringOn U).FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ X₁.M.ringOn U, ∃ b ∈ X₁.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ X₁.M.ringOn U) (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ X₁.M.ringOn U) (ρ' : (X₁.S.rechart c₀ hc (X₁.M.ringOn U) fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)) (u' : Sp (X₁.M.ringOn U) ⟶ F.X), IsAffineOpen U ∧ w ∈ U ∧ (∀ w' ∈ U, X₁.π w' ∈ Set.range i) ∧ Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X₁.ρ.i₀ ∧ IsDiagEnd F W ρ'.P u' ε' ∧ spMap (X₁.M.ringOn U).val.toRingHom ≫ u' = spMap X₁.S.R.val.toRingHom ≫ X₁.u := by
  intro g n F W Z i X₁ _hg1 _hn3 _hodd _himm he8 _hti _hproj ε₁ hε₁ w hw
  obtain ⟨U₀, u₀, hU₀a, hwU₀, hU₀i, hu₀⟩ := _root_.GlobalTheory.Poinc.ChartAt.exists_affine_chart_lift g n F W Z i X₁ w hw
  obtain ⟨P₁, hP₁⟩ := _root_.GlobalTheory.Poinc.exists_sharpOver_domain g n F W he8 (X₁.M.ringOn U₀) u₀
  have hN : 1 ≤ X₁.S.N := by have := X₁.S.N_ge; omega
  obtain ⟨U, h, P', φ, hUU₀, hUa, hwU, hφ, hφL, _hgφ, ⟨th, hth⟩, b, hb⟩ :=
    _root_.GlobalTheory.Poinc.exists_univBasis_affineChart X₁.o₁ X₁.Ω₁ X₁.M U₀ w hU₀a hwU₀ P₁ X₁.S.N hN
  have hne : ((U : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := ⟨w, hwU⟩
  have hsh : SharpOver F W P' (spMap (Subalgebra.inclusion h).toRingHom ≫ u₀) :=
    _root_.GlobalTheory.Poinc.sharpOver_baseChange g n F W _ _ P₁ P' u₀ _ φ hP₁ hφ hφL
  have hsp : spMap (X₁.M.ringOn U).val.toRingHom ≫ spMap (Subalgebra.inclusion h).toRingHom =
      spMap (X₁.M.ringOn U₀).val.toRingHom := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  have hcomp : spMap X₁.S.R.val.toRingHom ≫ X₁.u =
      spMap (X₁.M.ringOn U).val.toRingHom ≫ (spMap (Subalgebra.inclusion h).toRingHom ≫ u₀) := by
    rw [← Category.assoc, hsp, hu₀]
  obtain ⟨ε', hε', P₀, a, a', ε₀, ha, ha', hL, hL', hε₀⟩ :=
    _root_.GlobalTheory.Poinc.exists_common_fibre_diagEnd g n F W X₁.S.R (X₁.M.ringOn U) X₁.Ω₁ X₁.S.R.val.toRingHom (X₁.M.ringOn U).val.toRingHom X₁.ρ.P X₁.u ε₁ P' _
      hε₁ hsh hcomp
  have hg' : P'.g = X₁.S.g :=
    (_root_.GlobalTheory.polAV_g_eq_of_isGrpPullback X₁.Ω₁ _ P' P₀ _ a' ha').symm.trans ((_root_.GlobalTheory.polAV_g_eq_of_isGrpPullback X₁.Ω₁ _ X₁.ρ.P P₀ _ a ha).trans X₁.ρ.g_eq)
  have hyp : HypS P'.A P'.L :=
    _root_.GlobalTheory.Poinc.hypS_of_generic_ringOn X₁.o₁ X₁.Ω₁ X₁.M U hUa hne X₁.normal X₁.S.R X₁.ρ.P P' P₀ _ a a' ha ha' hL hL' X₁.ρ.hypS
  obtain ⟨pt', hadd, hbij, hweil, hmatch⟩ := _root_.GlobalTheory.Poinc.TorsExtend.exists_labelled_on_chart g n F W Z i X₁ U P' P₀ a a' hUa hne ha ha' hL hL'
  have fg : (X₁.M.ringOn U).FG := _root_.GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen X₁.o₁ X₁.Ω₁ X₁.M U hUa hne
  have frac : ∀ x : X₁.Ω₁, ∃ a ∈ X₁.M.ringOn U, ∃ b ∈ X₁.M.ringOn U, x = a / b := fun x => by
    obtain ⟨p, q, -, e⟩ := RatModel.exists_eq_div hUa hne x
    exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨p, rfl⟩, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨q, rfl⟩, e⟩
  obtain ⟨c₀, hc, hthm, hevm, ρ', ε'', hSame, hi₀, hD⟩ :=
    _root_.GlobalTheory.Poinc.exists_real_rechart_of_univBasis g n F W Z i X₁ U ε₁ fg frac _ P' ε' P₀ a a' ε₀ pt' th b hUa hne hε₁ hε' ha ha' hL hL' hε₀ hg' hyp hadd hbij
      hweil hmatch hth hb
  exact ⟨U, c₀, hc, fg, frac, hthm, hevm, ρ', ε'', _, hUa, hwU, fun w' hw' => hU₀i w' (hUU₀ hw'), hSame, hi₀, hD,
    hcomp.symm⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionPointOfLatticeCharacterStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_toric_torsion_point_of_lattice_character : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ) (z : F), 1 ≤ k → z ^ k = 1 → ∀ c : D.toPre.X →+ ℤ, ∃ x : TFK (R := V) F ⟶ A.A, TorAt U F k z c x := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.exists_torAt | exact GlobalTheory.Poinc.Sep.Spz.exists_torAt | (intros; apply GlobalTheory.Poinc.Sep.Spz.exists_torAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusPairOfTorsionPointOverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_pair_of_torsion_point_over : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → w.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → ∃ p : QkPt D.toPre (FractionRing V) N, p.y = 0 ∧ p.g = g ∧ QkToAkU U.toUnifPre (FractionRing V) N p x := by
  first | exact @GlobalTheory.Poinc.Sep.LiesPair.exists_pair_of_liesOver | exact GlobalTheory.Poinc.Sep.LiesPair.exists_pair_of_liesOver | (intros; apply GlobalTheory.Poinc.Sep.LiesPair.exists_pair_of_liesOver <;> assumption)
end

