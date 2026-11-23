module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamOfIsPullDeg
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2063
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFamPull
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem PullB.vanMod {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X} {b : D.SecB k (hD.xe x)}
    {b' : D'.SecB k x} (H : PullB hD x b b') {I : Ideal R} {I' : Ideal R'} (hI : I ≤ I'.comap φ) {e : ℕ}
    (hb : VanMod I b e) : VanMod I' b' e := by
  have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ :=
    (Ideal.pow_right_mono hI _).trans (Ideal.le_comap_pow φ _)
  have hw : (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ D.P.A.hom = D'.P.A.hom ≫ specOf φ :=
    (pull_grp hD).1.w
  have hc := ExpGTrans.famφB_pull hD x
  unfold PullB at H
  have ht : thick R' I' e ≫ specOf φ =
      spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hle) ≫ thick R I e := by
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  obtain ⟨h, hh⟩ : ∃ h : pullback D'.P.A.hom (thick R' I' e) ⟶ pullback D.P.A.hom (thick R I e),
      h ≫ pullback.fst D.P.A.hom (thick R I e) = pullback.fst D'.P.A.hom (thick R' I' e) ≫
        hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) :=
    ⟨pullback.lift _ (pullback.snd D'.P.A.hom (thick R' I' e) ≫ spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hle)) (by
      rw [Category.assoc, hw, ← Category.assoc, pullback.condition, Category.assoc, ht, Category.assoc]),
      pullback.lift_fst _ _ _⟩
  intro q
  refine fn_ext fun y hy => ?_
  choose p hp using fun κ => exists_chart D.P.isLB ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))
    (D'.famφB x κ (pullback.fst D'.P.A.hom (thick R' I' e) y)))
  have e₁ := H _ (pullback.fst D'.P.A.hom (thick R' I' e)) y p q hp (Set.mem_iInter.1 hy)
  have hm : pullback.fst D.P.A.hom (thick R I e) (h y) ∈ LB.wchart D.P.L (D.famφB (hD.xe x)) p :=
    Set.mem_iInter.2 fun κ => by
      have a : h ≫ pullback.fst D.P.A.hom (thick R I e) ≫ D.famφB (hD.xe x) κ =
          pullback.fst D'.P.A.hom (thick R' I' e) ≫ D'.famφB x κ ≫
            hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) := by
        rw [← Category.assoc, hh, Category.assoc, ← hc κ]
      exact (congrArg (fun m => m y ∈ D.P.L.U (p κ)) a).mpr (hp κ)
  have z₀ : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens), f y ∈ U → gs f y U 0 = 0 := fun f y U h => by
    rw [gs_eq f y U h, map_zero, map_zero]
  rw [← hh] at e₁
  have e₂ := (Units.mul_right_eq_zero _).1 (e₁.symm.trans ((gs_pull h _ y _ hm _).symm.trans
    ((congrArg (gs h y _) (hb p)).trans (z₀ h y _ hm))))
  exact ((gs_pull (𝟙 _) _ y _ hy _).trans ((congrArg (fun m => gs m y _ _) (Category.id_comp _)).trans e₂)).trans
    (z₀ _ y _ hy).symm

theorem exists_intFam_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (D' : DegData W (maximalIdeal W)) (hD : IsPullDeg φ D.toPre D'.toPre), Function.Injective φ → IsLocalHom φ → ∀ (k : ℕ) (F : IntFam (maximalIdeal R) D.toPre k), ∃ F' : IntFam (maximalIdeal W) D'.toPre k, ∀ x, PullB hD x (F.f (hD.xe x)) (F'.f x) := by
  intro R _ _ _ _ D W _ _ _ φ D' hD _ hl k F
  choose f' hf' using fun x => (SecPull.existsUnique_secPull _ _ _ _ _ _ _ D.toPre.P.isLB D'.toPre.P.isLB hD.w
    hD.w_gen (Fin 4) (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) _ (ExpGTrans.famφB_pull hD x)
    (F.f (hD.xe x))).exists
  have s₁ : scal (DegPre.BF D.toPre (FractionRing R)).hom 1 = 1 := by rw [scal, map_one, map_one]
  have s₂ : scal (DegPre.BF D'.toPre (FractionRing W)).hom 1 = 1 := by rw [scal, map_one, map_one]
  obtain ⟨E, hE⟩ := exists_fam_of_isPullDeg GlobalTheory.allSixLaws.1.globalFns R W φ D.toPre D'.toPre hD k F.F F.f f'
    (fun α => s₁ ▸ F.ext α) hf'
  have hI : maximalIdeal R ≤ (maximalIdeal W).comap φ := fun a ha => map_nonunit φ a ha
  refine ⟨{ F := E, f := f', ext := fun α => s₂.symm ▸ hE α, small := fun e => ?_ }, hf'⟩
  exact ((F.small e).preimage hD.xe.injective.injOn).subset fun x hx hv => hx (PullB.vanMod (hf' x) hI hv)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegOfValWOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegCancelTop

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_psiOn_pull {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    ∃ ψ : PsiOn D' (specOf φ ⁻¹ᵁ hD.W), ∀ (x : D'.X) (Z : Scheme.{0}) (r : Z ⟶ (specOf φ ⁻¹ᵁ hD.W).toScheme) (z : Z) J J',
      Good D.P.L z J → Good D'.P.L z J' →
      val (hD.psiW.psi (hD.xe x)) (r ≫ (specOf φ ∣_ hD.W)) z J =
        (om hD.w z J J' (r ≫ (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left))⁻¹ * val (ψ.psi x) r z J' := by
  have hm : (specOf φ ∣_ hD.W) ≫ hD.W.ι = (specOf φ ⁻¹ᵁ hD.W).ι ≫ specOf φ := morphismRestrict_ι _ _
  have key : ∀ x : D'.X, ∃ a : LB.Gen (LB.LinComb D'.P.L (K := PUnit)
      (fun _ => (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left) (fun _ => -1)), a.IsGen ∧
      LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ a (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)))
        (LB.pullGen D'.P.L _ _ (D'.psi x) (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (specOf φ ⁻¹ᵁ hD.W).toScheme) (z : Z) J J',
      Good D.P.L z J → Good D'.P.L z J' →
      val (hD.psiW.psi (hD.xe x)) (r ≫ (specOf φ ∣_ hD.W)) z J =
        (om hD.w z J J' (r ≫ (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left))⁻¹ * val a r z J' := by
    intro x
    have hψ : (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left ≫ proj hD =
        (specOf φ ∣_ hD.W) ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left := by
      show (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
        (specOf φ ∣_ hD.W) ≫ hD.W.ι ≫ (D.c (hD.xe x)).left
      rw [hD.c_pr x, ← Category.assoc, ← Category.assoc, hm]
    obtain ⟨a, ha, H⟩ := DegPull.exists_pmaps ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB (K := PUnit)
      (ε := fun _ => -1) (specOf φ ∣_ hD.W) (fun _ => hψ) (hD.psiW.psi (hD.xe x)) (hD.psiW.psi_gen _)
    refine ⟨a, ha, corr_of_val D'.P.isLB fun y J' hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
    swap
    · have v := DegPull.pmaps_val (fun _ => hψ) H r z hJ hJ'
      rw [Fintype.prod_unique, zpow_neg_one] at v
      exact v
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have hz : ((jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (specOf φ ∣_ hD.W)) ≫ hD.W.ι =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ jK R' ≫ specOf φ := by
      rw [Category.assoc, hm, ← Category.assoc, morphismRestrict_ι, Category.assoc]
    obtain ⟨hp, P⟩ := ArcSpecialise.pmaps_psiOn hD hD.psiW _ _ hz x
    have v₁ := DegPull.pmaps_val (fun _ => hψ) H (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) y hJ hJ'
    have v₂ := DegPull.pmaps_val (fun _ => hp) P (𝟙 _) y hJ hJ'
    rw [val_pull hJ', val_pull hJ']
    rw [val_pull hJ, val_pull hJ'] at v₂
    simp only [Category.id_comp] at v₁ v₂ ⊢
    have hmor : (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (toUnit (TW (specOf φ ⁻¹ᵁ hD.W)) ≫ D'.c x).left =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ D'.xK x := by
      show (jK R' ∣_ (specOf φ ⁻¹ᵁ hD.W)) ≫ (specOf φ ⁻¹ᵁ hD.W).ι ≫ (D'.c x).left =
        (jK R' ⁻¹ᵁ (specOf φ ⁻¹ᵁ hD.W)).ι ≫ jK R' ≫ (D'.c x).left
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    rw [hmor] at v₁
    exact mul_left_cancel (v₁.symm.trans v₂)
  choose a ha hc hv using key
  exact ⟨⟨a, ha, hc⟩, hv⟩

end GlobalTheory.PullDegCancelTop

namespace GlobalTheory.Mum

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoGluedFromLinCombPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem trF_sum_elim {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    (φ₁ : K → (Y ⟶ X)) (φ₂ : K' → (Y ⟶ X)) (ε₁ : K → ℤ) (ε₂ : K' → ℤ) (r : Z ⟶ Y) (z : Z)
    (p p' : K → L.ι) (q q' : K' → L.ι) :
    trF (Sum.elim φ₁ φ₂) (Sum.elim ε₁ ε₂) r z (Sum.elim p q) (Sum.elim p' q') =
      trF φ₁ ε₁ r z p p' * trF φ₂ ε₂ r z q q' := by
  rw [trF, trF, trF, Fintype.prod_sum_type]; rfl

theorem trF_self' {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (hp : r z ∈ LB.wchart L φ p) :
    trF φ ε r z p p = 1 := by
  unfold trF
  refine Finset.prod_eq_one fun k _ => ?_
  rw [gm_self hL (r ≫ φ k) z (Set.mem_iInter.1 hp k), _root_.one_zpow]

theorem iso_linComb_pull_glue : ∀ {X X' Y : Scheme.{0}} {M : LB Y}, M.IsLB → ∀ {L' : LB X'}, L'.IsLB →
    ∀ {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (X' ⟶ Y)) (ε : K → ℤ) (ψ : K' → (X ⟶ Y)) (e : K' → ℤ)
    (F : X ⟶ X') (w₁ : LB.Iso L' (LB.LinComb M φ ε)), w₁.IsGen →
    ∀ (u : LB.Gen (LB.LinComb M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim ε (fun i => - e i)))), u.IsGen →
    ∃ w : LB.Iso (LB.LinComb M ψ e) (L'.pull F), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (J : (Z ⟶ Y) → M.ι), Good M z J → ∀ j' : L'.ι, F (f z) ∈ L'.U j' →
        gw w f z j' (fun i => J (f ≫ ψ i)) = (gv w₁ (f ≫ F) z (fun k => J ((f ≫ F) ≫ φ k)) j')⁻¹ * val u f z J := by
  intro X X' Y M hM L' hL' K K' _ _ φ ε ψ e F w₁ hw₁ u hu

  have memE : ∀ {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (p : K → M.ι) (q : K' → M.ι),
      F (f z) ∈ LB.wchart M φ p → f z ∈ LB.wchart M ψ q →
      f z ∈ LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p q) := by
    intro Z f z p q hp hq
    refine Set.mem_iInter.2 fun k => ?_
    cases k with
    | inl k => exact Set.mem_iInter.1 hp k
    | inr i => exact Set.mem_iInter.1 hq i

  have key : ∀ {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (j' : L'.ι) (q : K' → M.ι) (p p' : K → M.ι),
      F (f z) ∈ L'.U j' → f z ∈ LB.wchart M ψ q → F (f z) ∈ LB.wchart M φ p → F (f z) ∈ LB.wchart M φ p' →
      gm f z _ (u.s (Sum.elim p q)) * (gm (f ≫ F) z _ (w₁.s (p, j')))⁻¹ =
        gm f z _ (u.s (Sum.elim p' q)) * (gm (f ≫ F) z _ (w₁.s (p', j')))⁻¹ := by
    intro Z f z j' q p p' hj hq hp hp'
    have a := gen_trans hu f z (memE f z p q hp hq) (memE f z p' q hp' hq)
    rw [trF_sum_elim, trF_self' hM ψ _ f z q hq, _root_.mul_one] at a
    have b := gm_isGen hw₁ (f ≫ F) z p p' j' j' hp hp' hj hj
    have c : gm (f ≫ F) z _ ((LB.LinComb M φ ε).g p p') = trF (fun k => F ≫ φ k) ε f z p p' := by
      refine (gm_linComb M φ ε (f ≫ F) z p p' hp hp').trans ?_
      simp only [trF, Category.assoc]
    rw [c, gm_self hL' (f ≫ F) z hj, inv_one, _root_.mul_one] at b
    show gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p q)) (u.s (Sum.elim p q)) * (gv w₁ (f ≫ F) z p j')⁻¹ =
      gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p' q)) (u.s (Sum.elim p' q)) * (gv w₁ (f ≫ F) z p' j')⁻¹
    rw [a, b]
    generalize trF (fun k => F ≫ φ k) ε f z p p' = T
    generalize gm f z _ (u.s (Sum.elim p' q)) = U
    generalize gv w₁ (f ≫ F) z p' j' = V
    rw [_root_.mul_inv, _root_.mul_mul_mul_comm, _root_.mul_inv_cancel, _root_.one_mul]
  have glue : ∀ (j' : L'.ι) (q : K' → M.ι),
      ∃ s : Γ(X, (L'.pull F).U (fun _ => j') ⊓ (LB.LinComb M ψ e).U q)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (p : K → M.ι), F (f z) ∈ L'.U j' → f z ∈ LB.wchart M ψ q →
        F (f z) ∈ LB.wchart M φ p →
        gm f z _ s = gm f z _ (u.s (Sum.elim p q)) * (gm (f ≫ F) z _ (w₁.s (p, j')))⁻¹ := by
    intro j' q
    obtain ⟨W, hW⟩ : ∃ W : (K → M.ι) → X.Opens, ∀ p x, x ∈ W p ↔
        F x ∈ L'.U j' ∧ x ∈ LB.wchart M ψ q ∧ F x ∈ LB.wchart M φ p :=
      ⟨fun p => F ⁻¹ᵁ L'.U j' ⊓ (LB.wchart M ψ q ⊓ F ⁻¹ᵁ LB.wchart M φ p), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ p, W p ≤ (L'.pull F).U (fun _ => j') ⊓ (LB.LinComb M ψ e).U q := fun p x hx =>
      ⟨mem_pull.2 ((hW p x).1 hx).1, ((hW p x).1 hx).2.1⟩
    have l₁ : ∀ p, W p ≤ LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p q) := fun p x hx =>
      memE (𝟙 X) x p q ((hW p x).1 hx).2.2 ((hW p x).1 hx).2.1
    have l₂ : ∀ p, W p ≤ F ⁻¹ᵁ (LB.wchart M φ p ⊓ L'.U j') := fun p x hx =>
      ⟨((hW p x).1 hx).2.2, ((hW p x).1 hx).1⟩
    obtain ⟨v, hv⟩ : ∃ v : ∀ p, Γ(X, W p)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (p : K → M.ι), f z ∈ W p →
        gm f z (W p) (v p) = gm f z _ (u.s (Sum.elim p q)) * (gm (f ≫ F) z _ (w₁.s (p, j')))⁻¹ :=
      ⟨fun p => res (l₁ p) (u.s (Sum.elim p q)) * (res (l₂ p) (pullU F _ (w₁.s (p, j'))))⁻¹,
        fun Z f z p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f z (l₁ p) hz _)
          ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f z (l₂ p) hz _).trans (gm_pull f F z _ (l₂ p hz) _)))))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        choose p hp using fun k => exists_chart hM (φ k (F x))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, (hW p x).2 ⟨mem_pull.1 hx.1, hx.2, Set.mem_iInter.2 hp⟩⟩) v (fun p p' x hx => by
        have h₁ := (hW p x).1 hx.1
        have h₂ := (hW p' x).1 hx.2
        exact (hv _ (𝟙 X) x p hx.1).trans ((key (𝟙 X) x j' q p p' h₁.1 h₁.2.1 h₁.2.2 h₂.2.2).trans
          (hv _ (𝟙 X) x p' hx.2).symm))
    refine ⟨s, fun Z f z p hj hq hp => ?_⟩
    have hz := (hW p (f z)).2 ⟨hj, hq, hp⟩
    exact (gm_res f z (l₀ p) hz s).symm.trans ((congrArg (gm f z (W p)) (hs p)).trans (hv Z f z p hz))
  choose s hs using glue
  refine ⟨⟨fun P => s (P.1 PUnit.unit) P.2⟩, (isGen_iff _).2 ?_, ?_⟩
  · intro Z f z j j' (k : K' → M.ι) (k' : K' → M.ι) hj hj' hk hk'
    choose p hp using fun a => exists_chart hM (φ a (F (f z)))
    have hpm : F (f z) ∈ LB.wchart M φ p := Set.mem_iInter.2 hp
    show gm f z _ (s j k) = gm (f ≫ F) z _ (L'.g j j') * (gm f z _ ((LB.LinComb M ψ e).g k k'))⁻¹ *
      gm f z _ (s j' k')
    rw [hs j k Z f z p hj hk hpm, hs j' k' Z f z p hj' hk' hpm]
    have a := gen_trans hu f z (memE f z p k hpm hk) (memE f z p k' hpm hk')
    rw [trF_sum_elim, trF_self' hM (fun a => F ≫ φ a) ε f z p (Set.mem_iInter.2 fun a => Set.mem_iInter.1 hpm a), _root_.one_mul] at a
    have c : gm f z _ ((LB.LinComb M ψ e).g k k') = trF ψ e f z k k' := gm_linComb M ψ e f z k k' hk hk'
    have d : trF ψ (fun i => - e i) f z k k' = (trF ψ e f z k k')⁻¹ := by
      simp only [trF, zpow_neg, Finset.prod_inv_distrib]
    rw [d] at a
    have b := gm_isGen hw₁ (f ≫ F) z p p j j' hpm hpm hj hj'
    have c' : gm (f ≫ F) z _ ((LB.LinComb M φ ε).g p p) = 1 :=
      (gm_linComb M φ ε (f ≫ F) z p p hpm hpm).trans (trF_self' hM φ ε (f ≫ F) z p hpm)
    rw [c', _root_.one_mul] at b
    show gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p k)) (u.s (Sum.elim p k)) * (gv w₁ (f ≫ F) z p j)⁻¹ =
      gm (f ≫ F) z _ (L'.g j j') * (gm f z _ ((LB.LinComb M ψ e).g k k'))⁻¹ *
      (gm f z (LB.wchart M (Sum.elim (fun k => F ≫ φ k) ψ) (Sum.elim p k')) (u.s (Sum.elim p k')) * (gv w₁ (f ≫ F) z p j')⁻¹)
    rw [a, b, c]
    generalize trF ψ e f z k k' = T
    generalize gm f z _ (u.s (Sum.elim p k')) = U
    generalize gv w₁ (f ≫ F) z p j' = V
    generalize gm (f ≫ F) z _ (L'.g j j') = G
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · intro Z f z J hJ j' hj
    have hp : F (f z) ∈ LB.wchart M φ (fun k => J ((f ≫ F) ≫ φ k)) :=
      Set.mem_iInter.2 fun k => hJ ((f ≫ F) ≫ φ k)
    show gm f z _ (s j' (fun i => J (f ≫ ψ i))) = _
    rw [hs j' _ Z f z _ hj (hJ.mem ψ f) hp,
      val_of u f z J (Sum.elim (fun k => J ((f ≫ F) ≫ φ k)) (fun i => J (f ≫ ψ i)))
        (by rintro (k | i) <;> simp only [Sum.elim_inl, Sum.elim_inr, Category.assoc])]
    exact mul_comm _ _

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLambdaGeneratorZpowWithPeriods
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.TauTwist ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem degenerationPointOfLattice_zsmul (T : Over (Spec (CommRingCat.of R))) (n : ℤ) (b : D.X) : cP D T (n • b) = cP D T b ^ n := by
  let f : Multiplicative D.X →* (T ⟶ D.P.A) :=
    { toFun := fun x => cP D T x.toAdd
      map_one' := by simpa using cPoint_nsmul D T 0 0
      map_mul' := fun x y => cPoint_add D T _ _ }
  have := map_zpow f (Multiplicative.ofAdd b) n
  simpa [f] using this

theorem overSpec_comp_zpow_grpObj {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (y : T ⟶ D.P.A) (n : ℤ) :
    ρ ≫ y ^ n = (ρ ≫ y) ^ n := by
  let f : (T ⟶ D.P.A) →* (T' ⟶ D.P.A) :=
    { toFun := fun x => ρ ≫ x
      map_one' := MonObj.comp_one _
      map_mul' := fun x y => MonObj.comp_mul _ _ _ }
  exact map_zpow f y n

theorem value_tau_add_nsmul_mul_iteratedCube (hB : D.TauBimult) {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) (a₀ m v : D.X) (k : ℕ) :
    val (D.tau (a₀ + k • m) v) (𝟙 (TK R).left) z J *
        cubN (th D z J) k (cP D (TK R) a₀) (cP D (TK R) m) (cP D (TK R) v) =
      val (D.tau a₀ v) (𝟙 (TK R).left) z J * val (D.tau m v) (𝟙 (TK R).left) z J ^ k := by
  induction k with
  | zero => rw [zero_nsmul, add_zero]; simp [cubN]
  | succ k ih =>
    have e := val_tau_add (𝟙 (TK R)) hJ hB (a₀ + k • m) m v
    rw [cPoint_add, cPoint_nsmul] at e
    simp only [Over.id_left] at e
    rw [succ_nsmul, ← add_assoc, cubN, Finset.prod_range_succ]
    simp only [cubN] at ih
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    have ih' := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_pow] at e' ih' ⊢
    rw [succ_nsmul]
    linear_combination (norm := abel) e' + ih'

theorem exists_lamGen_zpow : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (n : ℤ),
    ∃ g : LB.Gen (LB.LinComb D.P.L (Sum.elim (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ n))
        (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A))) (Sum.elim Oε (fun l => -n * Oε l))), g.IsGen ∧
      ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val (D.tau a (n • b)) (𝟙 _) z J *
          val g (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J = val (D.tau a b) (𝟙 _) z J ^ n := by
  intro R _ _ D hB n
  have hL := D.P.isLB
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · obtain ⟨t, ht, hv⟩ := exists_cubN D.cub (1 : D.P.A ⊗ D.P.A ⟶ D.P.A) (snd D.P.A D.P.A) (fst D.P.A D.P.A) k
    have hF : FormEq
        ![(1 * snd D.P.A D.P.A ^ k * fst D.P.A D.P.A).left, (1 * snd D.P.A D.P.A ^ k).left,
          (1 * fst D.P.A D.P.A).left, (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left, (snd D.P.A D.P.A * fst D.P.A D.P.A).left,
          (snd D.P.A D.P.A).left, (fst D.P.A D.P.A).left, (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left]
        ![1, -1, -1, 1, -(k : ℤ), k, k, -(k : ℤ)]
        (Sum.elim (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ (k : ℤ)))
          (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A)))
        (Sum.elim Oε (fun l => -(k : ℤ) * Oε l)) := by
      intro U _ h
      have e1 : (1 * snd D.P.A D.P.A ^ k * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) =
          fst D.P.A D.P.A * snd D.P.A D.P.A ^ (k : ℤ) := by rw [_root_.one_mul, zpow_natCast, mul_comm]
      have e2 : (1 * snd D.P.A D.P.A ^ k : D.P.A ⊗ D.P.A ⟶ D.P.A) = snd D.P.A D.P.A ^ (k : ℤ) := by
        rw [_root_.one_mul, zpow_natCast]
      have e3 : (1 * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A := _root_.one_mul _
      have e4 : (snd D.P.A D.P.A * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A * snd D.P.A D.P.A :=
        mul_comm _ _
      rw [e1, e2, e3, e4, Fintype.prod_sum_type]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, GlobalTheory.PolDeg.lamPts, Oε, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      abel
    obtain ⟨g, hg, hgv⟩ := exists_gen hL hF t ht
    refine ⟨g, hg, fun a b z J hJ => ?_⟩
    rw [hgv _ _ z J hJ, hv (TK R) _ z J hJ, MonObj.comp_one, lift_fst, lift_snd]
    have e := val_tau_nsmul (𝟙 (TK R)) hJ hB k b a
    rw [val_tau_symm _ hJ (k • b) a, val_tau_symm _ hJ b a] at e
    simp only [Over.id_left] at e
    rw [natCast_zsmul, zpow_natCast]
    exact e
  · obtain ⟨t, ht, hv⟩ := exists_cubN D.cub (snd D.P.A D.P.A ^ (-(k : ℤ))) (snd D.P.A D.P.A) (fst D.P.A D.P.A) k
    have hF : FormEq
        ![(snd D.P.A D.P.A ^ (-(k : ℤ)) * snd D.P.A D.P.A ^ k * fst D.P.A D.P.A).left,
          (snd D.P.A D.P.A ^ (-(k : ℤ)) * snd D.P.A D.P.A ^ k).left,
          (snd D.P.A D.P.A ^ (-(k : ℤ)) * fst D.P.A D.P.A).left, (snd D.P.A D.P.A ^ (-(k : ℤ))).left,
          (snd D.P.A D.P.A * fst D.P.A D.P.A).left,
          (snd D.P.A D.P.A).left, (fst D.P.A D.P.A).left, (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left]
        (fun i => -(![1, -1, -1, 1, -(k : ℤ), k, k, -(k : ℤ)] : Fin 8 → ℤ) i)
        (Sum.elim (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ (-(k : ℤ))))
          (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A)))
        (Sum.elim Oε (fun l => -(-(k : ℤ)) * Oε l)) := by
      intro U _ h
      have e0 : (snd D.P.A D.P.A ^ (-(k : ℤ)) * snd D.P.A D.P.A ^ k : D.P.A ⊗ D.P.A ⟶ D.P.A) = 1 := by
        rw [zpow_neg, zpow_natCast, inv_mul_cancel]
      have e4 : (snd D.P.A D.P.A * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A * snd D.P.A D.P.A :=
        mul_comm _ _
      have e5 : (snd D.P.A D.P.A ^ (-(k : ℤ)) * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) =
          fst D.P.A D.P.A * snd D.P.A D.P.A ^ (-(k : ℤ)) := mul_comm _ _
      rw [e0, _root_.one_mul, e4, e5, Fintype.prod_sum_type]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, GlobalTheory.PolDeg.lamPts, Oε, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      abel
    obtain ⟨g, hg, hgv⟩ := exists_gen hL hF (LB.invGen _ _ _ t) (DVR.invGen_isGen _ _ _ _ ht)
    refine ⟨g, hg, fun a b z J hJ => ?_⟩
    rw [hgv _ _ z J hJ, val_inv, hv (TK R) _ z J hJ, overSpec_comp_zpow_grpObj, lift_fst, lift_snd]
    have c1 : (toUnit (TK R) ≫ D.c b) ^ (-(k : ℤ)) = cP D (TK R) ((-(k : ℤ)) • b) := (degenerationPointOfLattice_zsmul _ _ _).symm
    rw [c1]
    have e := value_tau_add_nsmul_mul_iteratedCube hB hJ ((-(k : ℤ)) • b) b a k
    have z0 := val_tau_nsmul (𝟙 (TK R)) hJ hB 0 b a
    rw [zero_nsmul] at z0
    simp only [Over.id_left, pow_zero, cubN, Finset.range_zero, Finset.prod_empty, _root_.mul_one] at z0
    have s0 : (-(k : ℤ)) • b + k • b = 0 := by rw [← natCast_zsmul, ← add_smul, neg_add_cancel, zero_smul]
    rw [s0, z0, _root_.one_mul] at e
    have s1 := val_tau_symm (𝟙 (TK R)) hJ a ((-(k : ℤ)) • b)
    have s2 := val_tau_symm (𝟙 (TK R)) hJ a b
    simp only [Over.id_left] at s1 s2
    rw [s1, s2]
    rw [show cubN (th D z J) k (cP D (TK R) ((-(k : ℤ)) • b)) (toUnit (TK R) ≫ D.c b) (toUnit (TK R) ≫ D.c a) =
      cubN (th D z J) k (cP D (TK R) ((-(k : ℤ)) • b)) (cP D (TK R) b) (cP D (TK R) a) from rfl, e,
      mul_inv_rev, zpow_neg, zpow_natCast, mul_comm (_ ^ k)⁻¹, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBasisSmoothCommGroupSchemeField
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieField

theorem exists_isLieBasis_field : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (g : ℕ),
    SmoothOfRelativeDimension g B.hom → ∃ y : Fin g → (epsR K ⟶ B), IsLieBasis y :=
  fun _ _ B _ _ _ hdim => GlobalTheory.KeyPow.exists_isLieBasis B hdim

end GlobalTheory.LieField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleDescentFiniteFlat
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBDescent

theorem exists_descent : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Y] (L : LB X), L.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, GlobalTheory.LBDescent.chart f L i j)ˣ), GlobalTheory.LBDescent.DescCompat f L φ → GlobalTheory.LBDescent.DescCocycle f L φ → ∃ L' : LB Y, L'.IsLB ∧ LBIso L (L'.pull f) := by
  intro X Y f _ _ _ _ L hL φ hc hcoc
  refine _root_.GlobalTheory.LBDescent.exists_lb_of_invariant_frames f L hL φ fun y => ?_
  obtain ⟨V, hy, t, ht⟩ := _root_.GlobalTheory.LBDescent.exists_trivial_near_fibre f L hL y
  obtain ⟨c, hct, hcc⟩ := GlobalTheory.T.descentDatum_frame_cocycle_unit f L hL φ hc hcoc V t ht
  obtain ⟨V', hle, hy', u, hu⟩ := _root_.GlobalTheory.LBDescent.coboundary_locally_of_cocycle f V c hcc y hy
  exact ⟨V', hy', _root_.GlobalTheory.LBDescent.twist_frame_descent f L φ V t ht c hct V' hle u hu⟩

end GlobalTheory.LBDescent
end

