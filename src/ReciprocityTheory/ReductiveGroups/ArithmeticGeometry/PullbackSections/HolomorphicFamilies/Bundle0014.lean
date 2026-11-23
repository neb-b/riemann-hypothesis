module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigRamVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextChangeSecondFactor
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
public import Mathlib
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalRingCardinality.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigRamHelp
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam

open Formalism.L2.Pj

section Induce

variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {k : Type} [Field k] [Algebra V k]
  [IsFractionRing V k]

end Induce

theorem vLa_pos {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp0 : p ≠ 0)
    (hp : (p : 𝓞 K) ∈ la.asIdeal) : 0 < vLa la (p : K) := by
  have h1 : la.valuation K (algebraMap (𝓞 K) K (p : 𝓞 K)) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem la _).2 hp
  have h2 : la.valuation K (algebraMap (𝓞 K) K (p : 𝓞 K)) ≠ 0 := by
    rw [Ne, map_eq_zero, map_natCast]
    exact_mod_cast hp0
  have hlog := (WithZero.log_lt_log h2 one_ne_zero).2 h1
  rw [WithZero.log_one] at hlog
  unfold vLa
  rw [show ((p : K)) = algebraMap (𝓞 K) K (p : 𝓞 K) from (map_natCast _ _).symm]
  omega

section Host

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

end Host

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.MixEnd
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.MixEnd

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.PullbackSections

attribute [local instance] Over.cartesianMonoidalCategory

section Pmaps

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem val_pmaps' (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) (hm : PMaps w φ' φ ε a t h) {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z)
    (J₀ : (Z ⟶ X) → L.ι) (J : (Z ⟶ X') → L'.ι) (hJ₀ : Good L z J₀) (hJ : Good L' z J) :
    val t (r ≫ h) z J₀ =
      (∏ k, gw w (r ≫ φ' k) z (J₀ ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
  have hp : ∀ k, (r ≫ h) ≫ φ k = (r ≫ φ' k) ≫ F := fun k => by
    rw [Category.assoc, Category.assoc, hc]
  have h1 : ∀ k, F (φ' k (r z)) ∈ L.U (J₀ ((r ≫ h) ≫ φ k)) := by
    intro k
    convert hJ₀ ((r ≫ h) ≫ φ k) using 2
    rw [hp]
    first | rfl | simp
  have h2 : ∀ k, φ' k (r z) ∈ L'.U (J (r ≫ φ' k)) := fun k => hJ (r ≫ φ' k)
  have key := hm Z r z (fun k => J₀ ((r ≫ h) ≫ φ k)) (fun k => J (r ≫ φ' k)) h1 h2
  unfold val
  refine key.trans ?_
  simp only [hp]

end Pmaps

theorem val_rigPow {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left) (rig : LB.Gen (L.pull (eSec A))) (k : ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    val (rigPow A L rig k) r z J = (val (L := L) (K := PUnit) (φ := fun _ => eSec A) (ε := fun _ => 1) rig r z J) ^ k := by
  unfold val
  simp only [rigPow]
  exact map_zpow _ _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
  {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)

section Snd

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left}

theorem genSnd_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : PGen w)
    (eA : A.left ⟶ A.left) (eG : G.left ⟶ G.left) (hce : eA ≫ φ = φ ≫ eG) (ε : Fin 2 → ℤ)
    (α₀' : LB.Gen (LB.LinComb L₁ ![𝟙 A.left, eA] ε)) (α₀ : LB.Gen (LB.LinComb L₀ ![𝟙 G.left, eG] ε))
    (hPM : PMaps w ![𝟙 A.left, eA] ![𝟙 G.left, eG] ε α₀' α₀ φ)
    (mA : T ⊗ A ⟶ A) (mG : T₀ ⊗ G ⟶ G) (hmA : mA.left = (snd T A).left ≫ eA)
    (hmG : mG.left = (snd T₀ G).left ≫ eG)
    (α : LB.Gen (LB.LinComb L₀ ![(snd T₀ G).left, mG.left] ε)) (hα : α.IsGen)
    (hαc : LB.Gen.Corr L₀ _ _ _ _ α (LB.pullGen L₀ _ _ α₀ (snd T₀ G).left)) :
    ∃ α' : LB.Gen (LB.LinComb L₁ ![(snd T A).left, mA.left] ε), α'.IsGen ∧
      PMaps w ![(snd T A).left, mA.left] ![(snd T₀ G).left, mG.left] ε α' α (psiO hp τ hτ).left ∧
      LB.Gen.Corr L₁ _ _ _ _ α' (LB.pullGen L₁ _ _ α₀' (snd T A).left) := by
  have hc1 : ∀ k, (![(snd T A).left, mA.left] : Fin 2 → _) k ≫ φ =
      (psiO hp τ hτ).left ≫ (![(snd T₀ G).left, mG.left] : Fin 2 → _) k := by
    intro k; fin_cases k
    · exact (psi_snd hp τ hτ).symm
    · show mA.left ≫ φ = (psiO hp τ hτ).left ≫ mG.left
      rw [hmA, hmG, Category.assoc, hce, ← Category.assoc, ← psi_snd hp τ hτ, Category.assoc]
  have hc2 : ∀ k, (![𝟙 A.left, eA] : Fin 2 → _) k ≫ φ = φ ≫ (![𝟙 G.left, eG] : Fin 2 → _) k := by
    intro k; fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Category.id_comp, Category.comp_id]
    · exact hce
  obtain ⟨α', g', hm⟩ := exists_gen_move hL₀ hL₁ w hw _ _ ε (psiO hp τ hτ).left hc1 α hα
  refine ⟨α', g', hm, corr_of_val hL₁ fun y J hJ => ?_⟩
  choose J₀ hJ₀ using fun χ : (T ⊗ A).left ⟶ G.left => exists_chart hL₀ (χ y)
  have hJ₀' : Good L₀ y J₀ := hJ₀
  have p1 := val_pmaps' w hc1 hm (𝟙 _) y J₀ J hJ₀' hJ
  have p2 := val_pmaps' w hc2 hPM (snd T A).left y J₀ J hJ₀' hJ
  have c := val_corr hJ₀' hαc (psiO hp τ hτ).left
  rw [val_pull hJ₀', psi_snd hp τ hτ] at c
  rw [Category.id_comp, c, p2] at p1
  simp only [Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id,
    Category.id_comp, hmA] at p1
  rw [val_pull hJ, Category.id_comp]
  exact (mul_left_cancel p1).symm

end Snd

end ReciprocityTheory.ChartRestriction.G.PullbackSections.MixEnd
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NuChainPf
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

theorem secScal_cast {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {Y : Scheme.{0}} (h : Y ⟶ G.left)
    (k : ℕ) {L1 L2 : RigLB G} (e : L1 = L2)
    (s1 : LB.Sec (LB.LinComb L1.L (K := Fin 1) (fun _ => h) (fun _ => (k : ℤ))))
    (σ1 : LB.Sec (LB.LinComb L1.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (hs : GeneratorPullback.SecScal L1.L (fun _ : Fin 1 => h) (fun _ => (k : ℤ)) s1 (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ1 h 1) :
    GeneratorPullback.SecScal L2.L (fun _ : Fin 1 => h) (fun _ => (k : ℤ)) (e ▸ s1) (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ))
      (e ▸ σ1) h 1 := by
  subst e; exact hs

theorem nuReg : NuRegSt := by
  intro E _ _ _ H V _ _ _ _ _ t P _ ϖ hϖ Q hQ vK hvK tK m w _ k hk F hF
  obtain ⟨s, Ex, htie, hexp, hnu⟩ := hF
  haveI := t.semi.smooth
  haveI := t.semi.separated
  haveI := t.semi.quasiCompact
  obtain ⟨σ', hσ'⟩ := nuExt V ϖ hϖ P.D Q hQ vK hvK P.A t.G P.U k hk s Ex hexp hnu
  have hsc := secScal_cast (pullback.fst t.G.hom (Out.jK V)) k P.bundle s σ' hσ'
  refine ⟨P.bundle ▸ σ', fun Z r zp hzp z J J' hJ hJ' => ?_⟩
  have e1 := ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.secScal_sval hsc (r ≫ iotaK m) z hJ
  rw [Category.assoc, iotaK, pullback.lift_fst] at e1
  exact e1.trans (htie Z r zp hzp z J J' hJ hJ')

theorem zCast_trans {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k₁ k₂ k₃ : ℤ} (h : k₁ = k₂) (h' : k₂ = k₃)
    (F : LB.Sec (LPow A L k₁ T)) : zCast A h' (zCast A h F) = zCast A (h.trans h') F := by
  subst h; subst h'; rfl

theorem zCast_self {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k : ℤ} (h : k = k)
    (F : LB.Sec (LPow A L k T)) : zCast A h F = F := rfl

theorem regUnif_of (hN : NuDataSt) (hT : ThetaNuSt) (hM : MulNuSt) (hF : FinNuSt) : RegUnifSt := by
  intro E _ _ _ H V _ _ _ _ _ t P hTor θ _ M hMu tK m w hrig θK hθK t₀ F hVt
  obtain ⟨ϖ, Q, vK, hϖ, hQ, hvK⟩ := hN E H V t P
  obtain ⟨t', α₀, α, s₁, U, hok1, hok2, hα₀, hnorm, hαc, htw, hsym, hact⟩ := hVt
  have hM1 : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp at hMu
    · exact h
  have n0 := hT E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig θ θK hθK
  have n0' : NuK P Q vK m w 1 (zCast tK.G Nat.cast_one.symm (zCast tK.G Nat.cast_one θK)) := by
    rw [zCast_trans, zCast_self]; exact n0
  have n1 := hM E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig M hM1 (zCast tK.G Nat.cast_one θK) α₀ α s₁ n0'
    hα₀ hnorm hαc htw
  have hk : 0 < M ^ 2 := pow_pos hM1 2
  have n2 := hF E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig ((M : ℤ) ^ 2) (M ^ 2) (natCast_sq M) hk s₁ F t' U n1
    (by first | exact hok1 | exact hok2) hsym hact
  exact nuReg E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig (M ^ 2) hk (zCast tK.G (natCast_sq M) F) n2

theorem nuData : NuDataSt := by
  intro E _ _ _ H V _ _ _ _ _ t P
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  choose Q hQ using fun χ => QForm.exists_QVal hϖ P.D χ
  exact ⟨ϖ, Q, TG.vK hϖ, hϖ, hQ, TG.valOver_vK hϖ⟩

theorem regUnif_of' (hT : ThetaNuSt) (hM : MulNuSt) (hF : FinNuSt) : RegUnifSt := regUnif_of nuData hT hM hF

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NzdOfCompOfConn
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

theorem nzdOfComp_of_conn
    (hc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), IsPreconnected X.dom) :
    ReciprocityTheory.ChartRestriction.G.PullbackSections.NZDOfCompSt := by
  intro D T h j hj w F σ hσ hne w' G hFG
  have hFc : (F : T.R j) ∈ T.C j w := cutR_le T.C j w F.2
  have hGc : (G : T.R j) ∈ T.C j w' := cutR_le T.C j w' G.2
  have hmem : (F : T.R j) * (G : T.R j) ∈ cutR T.C j (WeightAlgebra.wadd w w') := by
    rw [cutR_eq T.C hj]; exact h.toLawsCore.mul j hj w w' _ hFc _ hGc
  have hval : (F : T.R j) * (G : T.R j) = 0 := by
    have h1 : incG deg (cutR T.C j) w F * incG deg (cutR T.C j) w' G = 0 := hFG
    rw [incG_mul deg (cutR T.C j) (deg_wadd w w') F G hmem] at h1
    have h2 := incG_inj deg (cutR T.C j) _ (h1.trans (map_zero _).symm)
    exact congrArg Subtype.val h2
  have hU := h.unf j hj σ hσ
  have hrd : rdU (T.U j σ) (F : T.R j) * rdU (T.U j σ) (G : T.R j) = 0 := by
    rw [← rdU_mul, hval, map_zero]
  have hFs := fun k => (hU.2.2.2.2.1 _ _ (dom_wtA w) _ (cusp_le_sec _ _ _ _ _ hFc) k).1
  have hGs := fun k => (hU.2.2.2.2.1 _ _ (dom_wtA w') _ (cusp_le_sec _ _ _ _ _ hGc) k).1
  have hG0 : ∀ k, ∀ y ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) (G : T.R j) k y = 0 := by
    intro k
    obtain ⟨x0, hx0, hx0ne⟩ := hne k
    exact eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom _) (hc _ _ _) (hFs k) (hGs k)
      (fun y _ => congrFun (congrFun hrd k) y) hx0 hx0ne
  have hsup : supN (T.U j σ).X (laU (T.U j σ) (wtA w') w'.n) (rdU (T.U j σ) (G : T.R j)) = 0 := by
    unfold supN supE
    have h0 : ∀ p : FPt (T.U j σ).X, ENNReal.ofReal (((T.U j σ).X p.1).pnorm (laU (T.U j σ) (wtA w') w'.n p.1)
        (rdU (T.U j σ) (G : T.R j) p.1) p.2) = 0 := by
      intro p
      unfold Data.pnorm
      rw [hG0 p.1 p.2 p.2.2]
      simp
    simp [h0]
  exact Subtype.ext (h.supDef j hj _ _ (dom_wtA w') σ hσ _ hGc hsup)

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SumSingleEmbeddingExtendLe
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTies1

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem cuspTie : CuspTieSt := by
  intro D T h j hj w hlast x P hP f hf
  exact h.thCusp j hj _ _ (dom_wtA w) hlast f ⟨x, P, hP, hf⟩

lemma sum_extendByZero_le_sum {p : ℕ} (g : Fin p → ℕ) (m : ℕ) : ∑ i : Fin m, ext0 g i ≤ ∑ i : Fin p, g i := by
  unfold ext0
  have hF : ∀ n : ℕ, (∑ i : Fin n, (if h : (i : ℕ) < p then g ⟨i, h⟩ else 0)) =
      ∑ k ∈ Finset.range n, (if h : k < p then g ⟨k, h⟩ else 0) := fun n =>
    Fin.sum_univ_eq_sum_range (fun k => if h : k < p then g ⟨k, h⟩ else 0) n
  have hg : (∑ i : Fin p, g i) = ∑ i : Fin p, (if h : (i : ℕ) < p then g ⟨i, h⟩ else 0) :=
    Finset.sum_congr rfl (fun i _ => by simp)
  rw [hg, hF m, hF p]
  calc ∑ k ∈ Finset.range m, (if h : k < p then g ⟨k, h⟩ else 0)
      ≤ ∑ k ∈ Finset.range (max m p), (if h : k < p then g ⟨k, h⟩ else 0) :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (le_max_left m p))
    _ = ∑ k ∈ Finset.range p, (if h : k < p then g ⟨k, h⟩ else 0) := by
        symm
        apply Finset.sum_subset (Finset.range_mono (le_max_right m p))
        intro k _ hk
        rw [Finset.mem_range] at hk
        rw [dite_eq_right hk]

open Classical in
lemma sum_single_embedding_extend_le {E : Type} [Field E] [NumberField E] (e : E →+* ℂ) (mult : (E →+* ℂ) → ℕ) {p : ℕ}
    (g : Fin p → ℕ) :
    ∑ τ : E →+* ℂ, ∑ i : Fin (mult τ), (if τ = e then ext0 g i else 0) ≤ ∑ i, g i := by
  rw [Finset.sum_eq_single e]
  · simp only [eq_self_iff_true, if_true]
    exact sum_extendByZero_le_sum g (mult e)
  · intro τ _ hτ
    exact Finset.sum_eq_zero (fun i _ => if_neg hτ)
  · intro h
    exact absurd (Finset.mem_univ e) h

open Classical in
lemma DF_wtA_le {D : D7} {j : ℕ} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H)
    (w : WeightFamilies.Wt D j) :
    DF Dw (wtA w) ≤ ∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i) := by
  have hswap : ∀ F : (τ : D.host.E →+* ℂ) → Fin (Dw.mult τ) → D.what₂.Tau → ℕ,
      ∑ τ, ∑ i : Fin (Dw.mult τ), ∑ t, F τ i t = ∑ t, ∑ τ, ∑ i : Fin (Dw.mult τ), F τ i t := by
    intro F
    calc ∑ τ, ∑ i : Fin (Dw.mult τ), ∑ t, F τ i t = ∑ τ, ∑ t, ∑ i : Fin (Dw.mult τ), F τ i t :=
          Finset.sum_congr rfl (fun τ _ => Finset.sum_comm)
      _ = ∑ t, ∑ τ, ∑ i : Fin (Dw.mult τ), F τ i t := Finset.sum_comm
  unfold Formalism.L2.Pj.DF wtA
  rw [hswap]
  apply Finset.sum_le_sum
  intro t _
  simp only [Finset.sum_add_distrib]
  exact add_le_add (by convert sum_single_embedding_extend_le (DV.tauEmb D t) Dw.mult (w.aP t))
    (by convert sum_single_embedding_extend_le (conjEmb (DV.tauEmb D t)) Dw.mult (w.aM t))

theorem dimPos_fr (D : D7) : 1 ≤ D.R.f ∧ 1 ≤ D.R.r := by
  refine ⟨?_, ?_⟩
  · have h1 := D.R.two_le_m
    have h2 := D.R.m_le_f
    exact le_trans (by omega : 1 ≤ D.R.m) h2
  · have h3 := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTies1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupAtUnit
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma dmin_ortho {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm x τ i‖ = 1 := by
  unfold dmin
  rw [hx τ]
  clear hx
  unfold lminor
  rw [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  apply Finset.prod_eq_one
  rintro a -
  simp only [Function.comp_apply]
  generalize (↑(Fin.castLE _ a) : ℕ) = b
  clear a
  clear x τ i
  unfold sgn
  split_ifs <;> simp

lemma pnorm_unit {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hu : ∀ τ i, ‖dmin X.Gm x τ i‖ = 1) : X.pnorm la P x = ‖P x‖ := by
  unfold Data.pnorm
  simp [hu]

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupGenTies
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem coprime_two_sq {R : Type*} [CommRing R] (I J : Ideal R) (M : ℕ) (hM : Odd M) (hI : (M : R) ∈ I)
    (hIJ : I ⊔ J = ⊤) : IsCoprime (Ideal.span {(2 : R)} * J ^ 2) I := by
  have h2 : IsCoprime (Ideal.span {(2 : R)}) I := by
    rw [Ideal.isCoprime_iff_exists]
    obtain ⟨k, hk⟩ := hM
    refine ⟨-(2 * (k : R)), ?_, (M : R), hI, ?_⟩
    · exact (Ideal.span {(2 : R)}).neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self 2))
    · rw [hk]; push_cast; ring
  have hJ : IsCoprime J I := by
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hIJ
  exact IsCoprime.mul_left h2 hJ.pow_left

theorem exists_rep {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N] (A B : Ideal R) (h : IsCoprime A B)
    (x : N) : ∃ x2 : N, x2 ∈ A • (⊤ : Submodule R N) ∧ x2 - x ∈ B • (⊤ : Submodule R N) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  refine ⟨a • x, Submodule.smul_mem_smul ha Submodule.mem_top, ?_⟩
  have hx : a • x + b • x = x := by rw [← add_smul, hab, one_smul]
  have e : a • x - x = -(b • x) := by
    calc a • x - x = a • x - (a • x + b • x) := by rw [hx]
      _ = -(b • x) := by abel
  rw [e]
  exact Submodule.neg_mem _ (Submodule.smul_mem_smul hb Submodule.mem_top)

theorem M_mem_Mb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
  have h1 : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.mem_span_singleton_self _
  rw [← l.prod] at h1
  exact Ideal.mul_le_left h1

theorem coprime_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    IsCoprime (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) l.Mb :=
  coprime_two_sq l.Mb _ l.M l.odd (M_mem_Mb l) l.coprime

theorem rep_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (l : Level H)
    (x : Dw.La) :
    ∃ x2 : Dw.La,
      x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La) ∧
      x2 - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
  exists_rep _ _ (coprime_level l) x

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end
end

