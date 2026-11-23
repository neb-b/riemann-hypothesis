module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ESecStruct
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumFCalculus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
namespace GlobalTheory.AdicSum
section
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E']


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E'] in
theorem _root_.GlobalTheory.AdicSum.sumI_unique [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥)
    {x : Ix → E} {s s' : E}
    (h : _root_.GlobalTheory.UT.SumI I x s) (h' : _root_.GlobalTheory.UT.SumI I x s') : s = s' := by
  classical
  obtain ⟨N, hN, hs, -, hconv⟩ := h
  obtain ⟨N', hN', hs', -, hconv'⟩ := h'
  set M := N ⊔ N' with hM
  have hMfg : M.FG := hN.sup hN'
  haveI : Module.Finite R M := Module.Finite.iff_fg.mpr hMfg
  have hmem : s - s' ∈ M := M.sub_mem (Submodule.mem_sup_left hs) (Submodule.mem_sup_right hs')
  have hpow : ∀ n : ℕ, (⟨s - s', hmem⟩ : M) ∈ I ^ n • (⊤ : Submodule R M) := by
    intro n
    obtain ⟨S, hS⟩ := hconv n
    obtain ⟨S', hS'⟩ := hconv' n
    have h1 := hS (S ∪ S') Finset.subset_union_left
    have h2 := hS' (S ∪ S') Finset.subset_union_right
    have h3 : s - s' ∈ I ^ n • M := by
      have e : s - s' = (s - ∑ i ∈ S ∪ S', x i) - (s' - ∑ i ∈ S ∪ S', x i) := by abel
      rw [e]
      exact Submodule.sub_mem _ (Submodule.smul_mono le_rfl le_sup_left h1)
        (Submodule.smul_mono le_rfl le_sup_right h2)
    rw [← Submodule.map_subtype_top M, ← Submodule.map_smul''] at h3
    obtain ⟨y, hy, hyeq⟩ := h3
    have hy' : y = ⟨s - s', hmem⟩ := Subtype.ext hyeq
    rwa [← hy']
  have h0 : (⟨s - s', hmem⟩ : M) = 0 := by
    rw [Ideal.jacobson_bot] at hI
    have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) I hI
    rw [← Submodule.mem_bot R, ← hK, Submodule.mem_iInf]
    exact hpow
  exact sub_eq_zero.mp (congrArg Subtype.val h0)


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E'] in
theorem _root_.GlobalTheory.AdicSum.sumI_map (f : E →ₗ[R] E') {x : Ix → E} {s : E}
    (h : _root_.GlobalTheory.UT.SumI I x s) :
    _root_.GlobalTheory.UT.SumI I (fun i => f (x i)) (f s) := by
  obtain ⟨N, hN, hs, hx, hconv⟩ := h
  refine ⟨N.map f, hN.map f, Submodule.mem_map_of_mem hs,
    fun i => Submodule.mem_map_of_mem (hx i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := hconv n
  refine ⟨S, fun T hT => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Submodule.map_smul'', ← map_sum, ← map_sub]
  exact Submodule.mem_map_of_mem (hS T hT)


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E'] in
theorem _root_.GlobalTheory.AdicSum.sumI_add {x x' : Ix → E} {s s' : E}
    (h : _root_.GlobalTheory.UT.SumI I x s) (h' : _root_.GlobalTheory.UT.SumI I x' s') :
    _root_.GlobalTheory.UT.SumI I (fun i => x i + x' i) (s + s') := by
  classical
  obtain ⟨N, hN, hs, hx, hconv⟩ := h
  obtain ⟨N', hN', hs', hx', hconv'⟩ := h'
  refine ⟨N ⊔ N', hN.sup hN', Submodule.add_mem_sup hs hs',
    fun i => Submodule.add_mem_sup (hx i) (hx' i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := hconv n
  obtain ⟨S', hS'⟩ := hconv' n
  refine ⟨S ∪ S', fun T hT => ?_⟩
  have e : s + s' - ∑ i ∈ T, (x i + x' i) = (s - ∑ i ∈ T, x i) + (s' - ∑ i ∈ T, x' i) := by
    rw [Finset.sum_add_distrib]; abel
  rw [e]
  exact Submodule.add_mem _
    (Submodule.smul_mono le_rfl le_sup_left (hS T (Finset.union_subset_left hT)))
    (Submodule.smul_mono le_rfl le_sup_right (hS' T (Finset.union_subset_right hT)))


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E'] in
theorem _root_.GlobalTheory.AdicSum.sumI_comp_iff {Jx : Type} {e : Jx → Ix}
    (he : Function.Injective e) {x : Ix → E}
    (h0 : ∀ i, i ∉ Set.range e → x i = 0) {s : E} :
    _root_.GlobalTheory.UT.SumI I (x ∘ e) s ↔ _root_.GlobalTheory.UT.SumI I x s := by
  classical
  constructor
  · rintro ⟨N, hN, hs, hx, hconv⟩
    refine ⟨N, hN, hs, fun i => ?_, fun n => ?_⟩
    · by_cases hi : i ∈ Set.range e
      · obtain ⟨j, rfl⟩ := hi
        exact hx j
      · rw [h0 i hi]
        exact N.zero_mem
    · obtain ⟨S, hS⟩ := hconv n
      refine ⟨S.map ⟨e, he⟩, fun T hT => ?_⟩
      rw [← Finset.sum_preimage e T he.injOn x (fun i _ hi => h0 i hi)]
      refine hS _ fun j hj => ?_
      rw [Finset.mem_preimage]
      exact hT (Finset.mem_map_of_mem _ hj)
  · rintro ⟨N, hN, hs, hx, hconv⟩
    refine ⟨N, hN, hs, fun j => hx (e j), fun n => ?_⟩
    obtain ⟨S, hS⟩ := hconv n
    refine ⟨S.preimage e he.injOn, fun T hT => ?_⟩
    have hpre : (T.map ⟨e, he⟩ ∪ S).preimage e he.injOn = T := by
      ext j
      simp only [Finset.mem_preimage, Finset.mem_union, Finset.mem_map,
        Function.Embedding.coeFn_mk, he.eq_iff, exists_eq_right]
      exact ⟨fun hj => hj.elim id fun hj => hT (Finset.mem_preimage.mpr hj), Or.inl⟩
    have hsum := hS (T.map ⟨e, he⟩ ∪ S) Finset.subset_union_right
    rw [← Finset.sum_preimage e _ he.injOn x (fun i _ hi => h0 i hi), hpre] at hsum
    exact hsum

end


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AdicSum.sumF_calculus : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R),
    _root_.ReciprocityTheory.ChartRestriction.G.Out.AdmBase R I → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (Ix : Type)
    (x x' : Ix → F) (s s' : F),
    (_root_.GlobalTheory.UT.SumF I F x s → _root_.GlobalTheory.UT.SumF I F x s' →
      s = s') ∧
    (_root_.GlobalTheory.UT.SumF I F x s → _root_.GlobalTheory.UT.SumF I F x' s' →
      ∀ c : F, _root_.GlobalTheory.UT.SumF I F (fun i => c * x i + x' i) (c * s + s')) ∧
    ∀ (Jx : Type) (e : Jx → Ix), Function.Injective e → (∀ i, i ∉ Set.range e → x i = 0) →
      (_root_.GlobalTheory.UT.SumF I F (x ∘ e) s ↔
        _root_.GlobalTheory.UT.SumF I F x s) := by
  intro R _ _ I hadm F _ _ Ix x x' s s'
  obtain ⟨hnoeth, -, -, hcomplete⟩ := hadm
  haveI := hnoeth
  haveI := hcomplete
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  refine ⟨fun h h' => _root_.GlobalTheory.AdicSum.sumI_unique (IsAdicComplete.le_jacobson_bot I) h h',
    fun h h' c => ?_, fun Jx e he h0 => _root_.GlobalTheory.AdicSum.sumI_comp_iff he h0⟩
  let f : F →ₗ[R] F :=
    { toFun := fun y => c * y
      map_add' := mul_add c
      map_smul' := fun r y => by
        show c * (algebraMap R (FractionRing R) r • y) = algebraMap R (FractionRing R) r • (c * y)
        exact Algebra.mul_smul_comm _ _ _ }
  exact _root_.GlobalTheory.AdicSum.sumI_add (_root_.GlobalTheory.AdicSum.sumI_map f h) h'

end GlobalTheory.AdicSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace TauPull

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem gm_injective_of_dense {Y Z : Scheme.{0}} [IsReduced Y] (h : Z ⟶ Y) (z : Z)
    (hd : ∀ V : Y.Opens, (V : Set Y).Nonempty → h z ∈ V) (V : Y.Opens) (hV : h z ∈ V) :
    Function.Injective (gm h z V) := by
  intro a b hab
  apply Units.ext
  have e := congrArg Units.val hab
  rw [gm_val h z V hV, gm_val h z V hV, ← sub_eq_zero, ← map_sub, ← map_sub] at e
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  have hm : z ∈ h ⁻¹ᵁ Y.basicOpen (a.val - b.val) :=
    hd _ (by
      by_contra hn
      exact hne (TopologicalSpace.Opens.not_nonempty_iff_eq_bot _ |>.1 hn))
  rw [Scheme.preimage_basicOpen, Scheme.mem_basicOpen _ _ z hV, e] at hm
  exact not_isUnit_zero hm

theorem corr_of_dense {X Y Z : Scheme.{0}} [IsReduced Y] [X.IsSeparated] {L : LB X} (hL : L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (h : Z ⟶ Y) (z : Z)
    (hd : ∀ V : Y.Opens, (V : Set Y).Nonempty → h z ∈ V)
    (H : ∀ J, Good L z J → val t h z J = val t' h z J) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  have dom : IsDominant h := ⟨dense_iff_inter_open.2 fun U hU hne => ⟨h z, hd ⟨U, hU⟩ hne, z, rfl⟩⟩
  refine unit_ext fun y hy => congrArg (gm (𝟙 Y) y _) ?_
  have hz : h z ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' := hd _ ⟨y, hy⟩
  apply gm_injective_of_dense h z hd _ hz
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (Sum.elim (fun k => h ≫ φ k) (fun k => h ≫ φ' k)) (Sum.elim j j') (by
    rintro (a | a) (b | b) e
    exacts [c₁ a b (ext_of_isDominant h e), c₃ a b (ext_of_isDominant h e),
      (c₃ b a (ext_of_isDominant h e.symm)).symm, c₂ a b (ext_of_isDominant h e)]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hz.1 a, Set.mem_iInter.1 hz.2 a])
  have := H J hJ
  rw [val_of t _ z J j (fun k => e (.inl k)), val_of t' _ z J j' (fun k => e (.inr k))] at this
  exact (gm_res _ z _ hz _).trans (this.trans (gm_res _ z _ hz _).symm)

theorem jK_mem {R : Type} [CommRing R] [IsDomain R] (z : (TK R).left) (V : (Spec (CommRingCat.of R)).Opens)
    (hV : (V : Set (Spec (CommRingCat.of R))).Nonempty) : jK R z ∈ V := by
  obtain ⟨x, hx⟩ := hV
  have hz : (jK R z).asIdeal ≤ x.asIdeal := by
    have h0 : PrimeSpectrum.asIdeal (R := FractionRing R) z = ⊥ := @Ideal.eq_bot_of_prime _ _ _ (PrimeSpectrum.isPrime _)
    intro r hr
    have h1 : algebraMap R (FractionRing R) r ∈ PrimeSpectrum.asIdeal (R := FractionRing R) z := hr
    rw [h0, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at h1
    rw [h1]; exact zero_mem _
  exact ((PrimeSpectrum.le_iff_specializes _ _).1 hz).mem_open V.isOpen hx

section OnW

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem val_tau {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J} (hJ : Good D.P.L z J) (a b : D.X) :
    val (D.tau a b) r z J =
      val (D.psi (a + b)) r z J * (val (D.psi a) r z J)⁻¹ * (val (D.psi b) r z J)⁻¹ * (val D.rigK r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem val_tauW (ψW : PsiOn D W) {Z : Scheme.{0}} (r : Z ⟶ (TW W).left) {z : Z} {J} (hJ : Good D.P.L z J)
    (a b : D.X) : val (ψW.tau a b) r z J =
      val (ψW.psi (a + b)) r z J * (val (ψW.psi a) r z J)⁻¹ * (val (ψW.psi b) r z J)⁻¹ * (val (D.rigW W) r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem tauW_corr (hB : D.TauBimult) (ψW : PsiOn D W) (hW : (W : Set (Spec (CommRingCat.of R))).Nonempty)
    (a a' b : D.X) : LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (ψW.tau (a + a') b)
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
          (lift (cP D (TW W) a) (lift (cP D (TW W) a') (cP D (TW W) b))).left))
      (LB.mulGen D.P.L _ _ _ _ (ψW.tau a b) (ψW.tau a' b)) := by
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨lam, hl⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact jK_mem y W hW), IsOpenImmersion.lift_fac _ _ _⟩
  have hκ : (lam ≫ jK R ∣_ W) ≫ W.ι = jK R := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hl, Category.id_comp]
  let κ : TK R ⟶ TW W := Over.homMk (lam ≫ jK R ∣_ W) hκ
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  have red : IsReduced (TW W).left := inferInstanceAs (IsReduced W.toScheme)
  refine corr_of_dense D.P.isLB κ.left z (fun V hV => ?_) fun J hJ => ?_
  · have h₁ : jK R z ∈ W.ι ''ᵁ V := jK_mem z _ (hV.image _)
    obtain ⟨y, hy, e⟩ := h₁
    have e' : W.ι y = W.ι (κ.left z) := e.trans (congrArg (fun q => q z) hκ).symm
    rw [← W.ι.isOpenEmbedding.injective e']
    exact hy
  · have vψ : ∀ χ, val (ψW.psi χ) κ.left z J = val (D.psi χ) (𝟙 _) z J := fun χ => by
      have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq χ) lam).trans (val_pull hJ _ _ _))
      rw [hl] at this
      exact this
    have vρ : val (D.rigW W) κ.left z J = val D.rigK (𝟙 _) z J := by
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      rw [Category.id_comp]
      exact congrArg (fun q => val D.rig q z J) hκ
    have vτ : ∀ a b, val (ψW.tau a b) κ.left z J = val (D.tau a b) (𝟙 _) z J := fun a b => by
      rw [val_tauW ψW _ hJ, val_tau _ hJ, vψ, vψ, vψ, vρ]
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    rw [vτ, vτ, vτ, ← e]
    refine congrArg₂ (· * ·) rfl ((val_cub D.cub κ hJ _ _ _).trans (Eq.trans ?_
      (val_cub D.cub (𝟙 (TK R)) hJ (cP D _ a) (cP D _ a') (cP D _ b)).symm))
    simp only [comp_cP]

theorem tauW_mul (hB : D.TauBimult) (ψW : PsiOn D W) {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TW W)
    {z : T.left} {J} (hJ : Good D.P.L z J) (a a' b : D.X) :
    val (ψW.tau (a + a') b) κ.left z J * th D z J (cP D T a) (cP D T a') (cP D T b) =
      val (ψW.tau a b) κ.left z J * val (ψW.tau a' b) κ.left z J := by
  have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (tauW_corr hB ψW ⟨_, (κ.left z).2⟩ a a' b) κ.left).trans
    (val_mul hJ _ _ _))
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
  refine Eq.trans ?_ (val_cub D.cub κ hJ (cP D _ a) (cP D _ a') (cP D _ b)).symm
  rw [comp_cP, comp_cP, comp_cP]

end OnW

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem val_psiW (hD : IsPullDeg φ D D') {y : (TK R').left} {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J')
    (χ : D'.X) : val (hD.psiW.psi (hD.xe χ)) hD.g y J =
      (gw hD.w (D'.xK χ) y (J (D'.xK χ ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) (J' (D'.xK χ)))⁻¹ *
        val (D'.psi χ) (𝟙 _) y J' := by
  obtain ⟨b, hb, hc⟩ := hD.psi_pr χ
  have e₂ := (val_corr hJ hc (𝟙 _)).trans (val_pull hJ _ _ _)
  rw [Category.id_comp] at e₂
  rw [← e₂]
  obtain ⟨p, hp⟩ : ∃ p, p = J (D'.xK χ ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = J' (D'.xK χ) := ⟨_, rfl⟩
  rw [← hp, ← hq, val_of b _ y J (fun _ => p) (fun _ => by rw [Category.id_comp, hp]),
    val_of (D'.psi χ) _ y J' (fun _ => q) (fun _ => by rw [Category.id_comp, hq])]
  have m₁ : (𝟙 (TK R').left : _ ⟶ _) y ∈ D'.xK χ ⁻¹ᵁ ((D.P.L.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).U
      (fun _ => p) ⊓ D'.P.L.U q) := ⟨mem_pull.2 (hp ▸ hJ _), hq ▸ hJ' _⟩
  have e₁ := congrArg (gm (𝟙 (TK R').left) y
    (D'.xK χ ⁻¹ᵁ ((D.P.L.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).U (fun _ => p) ⊓ D'.P.L.U q)))
    (hb (fun _ => p) q)
  refine (gm_res _ y _ m₁ _).symm.trans (e₁.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans ((congrArg (· ^ (-1 : ℤ)) (gm_pull _ (D'.xK χ) y
      ((D.P.L.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).U (fun _ => p) ⊓ D'.P.L.U q) m₁ _)).trans ?_))
      (gm_res _ y _ m₁ _))))
  rw [Category.id_comp]
  exact zpow_neg_one _

set_option maxHeartbeats 1000000 in
theorem tauBimult_pull (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') (hB : D.TauBimult) : D'.TauBimult := by
  intro a a' b
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  choose J hJ₀ using fun χ : (TK R').left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hJ : Good D.P.L y J := hJ₀
  have gp := pull_grp hD
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  let T : Over (Spec (CommRingCat.of R)) := Over.mk ((TK R').hom ≫ spMap φ)
  let κ : T ⟶ TW hD.W := Over.homMk hD.g hD.g_comm
  let β : (TK R' ⟶ D'.P.A) → (T ⟶ D.P.A) := fun x => pushPt gp.1.w x
  have βc : ∀ χ, β (cP D' _ χ) = cP D _ (hD.xe χ) := fun χ => Over.OverMorphism.ext (by
    show ((TK R').hom ≫ (D'.c χ).left) ≫ Φ = ((TK R').hom ≫ spMap φ) ≫ (D.c (hD.xe χ)).left
    rw [Category.assoc, hD.c_pr, Category.assoc])
  let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ := fun x => gw hD.w x.left y (J (x.left ≫ Φ)) (J' x.left)
  let θ : (T ⟶ D.P.A) → (T ⟶ D.P.A) → (T ⟶ D.P.A) → ((TK R').left.presheaf.stalk y)ˣ := th D (T := T) y J
  have cub : ∀ a b c : TK R' ⟶ D'.P.A, θ (β a) (β b) (β c) =
        Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
          th D' y J' a b c := by
    intro a b c
    have e := cub_pull hG hD (T' := TK R') hJ hJ' a b c
    have q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 = (lift (β a) (lift (β b) (β c))).left :=
      hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => gw hD.w q y (J (q ≫ Φ)) (J' q))) rfl)
  have vψ : ∀ χ, val (hD.psiW.psi (hD.xe χ)) hD.g y J = (Ω (cP D' _ χ))⁻¹ * val (D'.psi χ) (𝟙 _) y J' :=
    fun χ => val_psiW hD hJ hJ' χ
  have vρ : val (D.rigW hD.W) hD.g y J = Ω 1 * val D'.rigK (𝟙 _) y J' := by
    have pm := (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le Φ (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
    have a₂ : ((TK R').hom ≫ specOf φ) ≫ eSec D.P.A = (1 : TK R' ⟶ D'.P.A).left ≫ Φ :=
      congrArg (fun q => q.left) (map_one (pushHom gp (TK R'))).symm
    have e := pm _ (TK R').hom y (fun _ => J ((1 : TK R' ⟶ D'.P.A).left ≫ Φ))
      (fun _ => J' (1 : TK R' ⟶ D'.P.A).left) (fun _ => hJ _) (fun _ => hJ' _)
    rw [Fintype.prod_unique, zpow_one] at e
    have b₁ : hD.g ≫ (toUnit (TW hD.W)).left = (TK R').hom ≫ specOf φ := hD.g_comm
    have b₂ : 𝟙 _ ≫ (toUnit (TK R')).left = (TK R').hom := Category.id_comp _
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
    rw [b₁, b₂]
    exact (val_of _ _ y J _ (fun _ => congrArg J a₂)).trans e
  have key : val (hD.psiW.tau (hD.xe a + hD.xe a') (hD.xe b)) hD.g y J *
      θ (cP D T (hD.xe a)) (cP D T (hD.xe a')) (cP D T (hD.xe b)) =
      val (hD.psiW.tau (hD.xe a) (hD.xe b)) hD.g y J * val (hD.psiW.tau (hD.xe a') (hD.xe b)) hD.g y J :=
    tauW_mul hB hD.psiW κ hJ _ _ _
  rw [← βc, ← βc, ← βc, cub, val_tauW _ _ hJ, val_tauW _ _ hJ, val_tauW _ _ hJ, ← map_add (f := _), ← map_add (f := _), ← map_add (f := _),
    ← map_add, vψ, vψ, vψ, vψ, vψ, vψ, vψ, vρ, cPoint_add, cPoint_add, cPoint_add, cPoint_add] at key
  refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
  refine (congrArg₂ (· * ·) rfl (val_cub D'.cub (𝟙 (TK R')) hJ' (cP D' _ a) (cP D' _ a') (cP D' _ b))).trans ?_
  rw [Category.id_comp, Category.id_comp, Category.id_comp, val_tau _ hJ', val_tau _ hJ', val_tau _ hJ']
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end Pull

end TauPull

theorem tauBimult_of_isPullDeg : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (_hD : IsPullDeg φ D D'), D.TauBimult → D'.TauBimult :=
  fun hG _ _ _ _ _ _ _ _ _ hD hB => TauPull.tauBimult_pull hG hD hB

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfLevels
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoordLinear

open Geo.Tor

theorem fn_eq_of_levels {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    (W : (Spec (CommRingCat.of R)).Opens) (hW : W = ⊤) (a b : Γ(Spec (CommRingCat.of R), W))
    (h : ∀ e, ((thick R I e).app W).hom a = ((thick R I e).app W).hom b) : a = b := by
  subst hW
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  have key : ∀ (e : ℕ) (c : Γ(Spec (CommRingCat.of R), ⊤)),
      Ideal.Quotient.mk (I ^ (e + 1)) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) =
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (e + 1)))).hom.hom (((thick R I e).app ⊤).hom c) := fun e c =>
    (congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))).symm
  have := IsHausdorff.StrictMono.funext' I (a := fun n => n + 1) (strictMono_id.add_const 1)
    (f := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a)
    (g := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b)
    (fun n _ => (key n a).trans ((congrArg _ (h n)).trans (key n b).symm))
  exact congrFun this ()

end GlobalTheory.CoordLinear
end

