module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0911
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0921
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsOddNeZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleArithHilbertSamuelLargeRadiusPair
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem ampleHS_pair : AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p) (a b a' b' : ℤ) (M : HermLB p) (α : ℝ), P.Rep a b M → IsAmpleLB M.B →
    M.SemiPos D → M.IsSelfInter α → ∃ t₀ : ℝ, ∀ t, t₀ ≤ t →
      Tendsto (fun m : ℕ => P.lc (m * a + a') (m * b + b') (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop
        (𝓝 (α / (D + 1).factorial + (((D : ℝ) + 1) * gdeg M D / (D + 1).factorial) * t)) := by
  intro hHS k _ X _ p D hX P a b a' b' M α hM hamp hsemi hself
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.VolBr.Pair.exists_rep k X p P a' b'
  obtain ⟨Q, hQL, hQA, hQB⟩ := _root_.GlobalTheory.HSNef.change_pair k X p P a b a' b' M N hM hN
  have hamp' : IsAmpleLB Q.L.B := by rw [hQL]; exact hamp
  have hsemi' : Q.L.SemiPos D := by rw [hQL]; exact hsemi
  have hself' : Q.L.IsSelfInter α := by rw [hQL]; exact hself
  obtain ⟨t₀, ht⟩ := hHS k X p D hX Q α hamp' hsemi' hself'
  refine ⟨t₀, fun t htt => ?_⟩
  have hlc : ∀ m : ℕ, Q.lc m 1 (Real.exp (t * m)) = P.lc (m * a + a') (m * b + b') (Real.exp (t * m)) := by
    intro m
    simp only [Pair.lc]
    rw [hQB, one_mul, one_mul]
  have e : (α + ((D : ℝ) + 1) * t * gdeg Q.L D) / ((D + 1).factorial : ℝ) =
      α / (D + 1).factorial + (((D : ℝ) + 1) * gdeg M D / (D + 1).factorial) * t := by
    rw [hQL]; ring
  have h := ht t htt
  rw [e] at h
  simpa only [hlc] using h

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidConstant
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic TopologicalSpace GlobalTheory.EndDivisible

theorem exists_relation_of_cls (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Sp K) (hf : Smooth f)
    (hp : GlobalTheory.AbLaw.IsProjBy f) (c : Pic X) :
    ∃ n : ℕ, ∀ (B : LB X) (hB : B.IsLB), cls B hB = c → ∀ σ : Fin n → LB.Sec B,
      ∃ a : Fin n → K, a ≠ 0 ∧ ∀ i, ∑ k, GlobalTheory.AbLaw.cst f (B.U i) (a k) * (σ k).f i = 0 := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  obtain ⟨Q⟩ := GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy K X f hf hp M hM
  refine ⟨Q.a + 1, fun B hB hc σ => ?_⟩
  obtain ⟨w, hw⟩ := (cls_eq_iff hB hM).1 hc
  let e : LB.Sec B ≃ₗ[Γ(X, ⊤)] LB.Sec M :=
    (GlobalTheory.AbLaw.SecOn.topEquiv B).symm ≪≫ₗ GlobalTheory.AbLaw.SecOn.congr hB hM w hw ⊤ ≪≫ₗ GlobalTheory.AbLaw.SecOn.topEquiv M
  obtain ⟨a, ha, h⟩ := Q.exists_relation (fun k => e (σ k))
  let a' : Fin (Q.a + 1) → Γ(X, ⊤) := fun k =>
    f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a k))
  have ev : ∀ (N : LB X) (τ : Fin (Q.a + 1) → LB.Sec N) (i : N.ι),
      (∑ k, a' k • τ k).f i = ∑ k, GlobalTheory.AbLaw.cst f (N.U i) (a k) * (τ k).f i := fun N τ i => by
    let F : LB.Sec N →+ Γ(X, N.U i) := AddMonoidHom.mk' (fun s => s.f i) (fun _ _ => rfl)
    exact map_sum F _ _
  have h1 : ∑ k, a' k • e (σ k) = 0 :=
    GlobalTheory.AbLaw.HighTwist.sec_eq_zero _ fun i => (ev M _ i).trans (h i)
  have h2 : ∑ k, a' k • σ k = 0 := by
    apply e.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero, ← h1]
    exact Finset.sum_congr rfl fun k _ => e.map_smul _ _
  exact ⟨a, ha, fun i => (ev B σ i).symm.trans (by rw [h2]; rfl)⟩

theorem eff_nsmul_of_pos {X : Scheme.{0}} [IsIntegral X] (c : Pic X) (hc : GlobalTheory.EffBound.Eff c) (N : ℕ)
    (hN : 1 ≤ N) : GlobalTheory.EffBound.Eff (N • c) := by
  induction N, hN using Nat.le_induction with
  | base => rwa [one_nsmul]
  | succ n _ ih => rw [succ_nsmul]; exact GlobalTheory.EffBound.eff_add _ _ ih hc

theorem exists_pull_monomial {X W Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (w : W ⟶ X) (N : ℕ)
    (s s' : LB.Sec (LB.LinComb L (K := Fin N) (fun _ => w) (fun _ => 1))) (t : ℕ)
    (f : Z ⟶ W) (u : Z ⟶ X) (hu : u = f ≫ w) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) (a : ℕ) (ha : a ≤ t) :
      ∃ σ : LB.Sec (LB.LinComb L (K := Unit) (fun _ => u) (fun _ => ((N * t : ℕ) : ℤ))),
        sval σ (𝟙 Z) z J = sval s' f z J ^ a * sval s f z J ^ (t - a) := by
  have hF : FormEq (K := (Fin a ⊕ Fin (t - a)) × Fin N) (fun _ => f ≫ w) (fun _ => 1)
      (fun _ : Unit => u) (fun _ => ((N * t : ℕ) : ℤ)) := by
    intro U _ h
    rw [hu]
    simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_sum, Fintype.card_fin, Fintype.card_unit, pow_one, Nat.add_sub_of_le ha, zpow_natCast]
    rw [mul_comm]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF
    (pullSec (powSec (I := Fin a ⊕ Fin (t - a)) (Sum.elim (fun _ => s') (fun _ => s))) f)
  refine ⟨σ, (hσ _ _ z J hJ).trans ((sval_pullSec _ _ _ z hJ).trans ?_)⟩
  rw [sval_powSec _ _ z hJ, Fintype.prod_sum_type, Category.id_comp]
  simp

theorem constSt : ConstSt := by
  intro K _ _ A _ hA L hL hamp m
  have := hA.proper
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : A.left.IsSeparated := ⟨by
    rw [← terminal.comp_from A.hom]; infer_instance⟩
  have hproj : GlobalTheory.AbLaw.IsProjBy A.hom := by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K A L hL).1 hamp
    exact ⟨_, GlobalTheory.AbLaw.isLB_pw hL d, n, s, hs⟩
  let E := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have hk : IsField Γ(Spec (CommRingCat.of K), ⊤) := E.toMulEquiv.isField (Field.toIsField K)
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hamp ⊤ (isAffineOpen_top _)
  obtain ⟨n, hn⟩ := exists_relation_of_cls K A.left A.hom hA.smooth hproj (N • m)
  refine ⟨n, fun t hnt ψ hψ heff => ?_⟩
  obtain ⟨P, hP, hPc, ε, p₀, hε⟩ := eff_nsmul_of_pos _ heff N hN
  have hQ := LB.isLB_linComb hL (K := Unit) (fun _ => ψ.left) (fun _ => ((N * t : ℕ) : ℤ))
  have hT : cls _ (isLB_tens hP hQ) = N • m := by
    rw [cls_tens hP hQ, hPc, cls_linComb hL, Fintype.sum_unique, natCast_zsmul, nsmul_sub, mul_nsmul',
      sub_add_cancel]
  let w := (A.hom ⁻¹ᵁ ⊤).ι
  let f : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme := IsOpenImmersion.lift w ψ.left (by
    rintro _ -
    rw [Scheme.Opens.range_ι]
    trivial)
  have hf : f ≫ w = ψ.left := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨z⟩ : Nonempty A.left := inferInstance
  obtain ⟨i, hi⟩ : ∃ i, f z ∈ nonzeroLocus (s i) := Opens.mem_iSup.1 (by rw [hcov]; trivial)
  obtain ⟨hD, r, hr, hsurj⟩ := hs i
  obtain ⟨J, hJ⟩ : ∃ J, Good L z J := by
    choose I hI using fun χ : A.left ⟶ A.left => exists_chart hL (χ z)
    exact ⟨I, hI⟩
  obtain ⟨p, hp⟩ := exists_chart hP z
  have hεz : gs (𝟙 _) z (P.U p) (ε.f p) ≠ 0 := by
    rw [gs_eq (𝟙 _) z (P.U p) hp]
    exact GlobalTheory.EffBound.germ_sec_ne_zero ε hε p z hp
  let κ := germPull A.hom z ⊤ trivial
  let ρ := germPull f z _ hi
  have hy : IsUnit (sval (s i) f z J) := by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hi
    exact isUnit_sval (s i) f z hJ k hk
  have hrj : ∀ j, ρ (r j) ∈ κ.range := fun j => by
    have e : sval (s j) f z J = ρ (r j) * sval (s i) f z J := by
      have hm := hJ.mem (K := Fin N) (fun _ => w) f
      have hm' : f z ∈ nonzeroLocus (s i) ⊓ (powOver A L ⊤ N).U (fun _ => J (f ≫ w)) := ⟨hi, hm⟩
      have := congrArg (gs f z _) (hr j (fun _ => J (f ≫ w)))
      rw [gs_mul f z _ hm', gs_res f z _ hm', gs_res f z _ hm', gs_res f z _ hm'] at this
      rw [germPull_apply]
      exact this
    choose σ hσ using fun a : Fin n =>
      exists_pull_monomial L hL w N (s i) (s j) t f ψ.left hf.symm z J hJ a (a.2.le.trans hnt)
    obtain ⟨c, hc, h0⟩ := hn _ _ hT (fun a => GlobalTheory.EffBound.tensSec ε (σ a))
    have hm₂ := hJ.mem (K := Unit) (fun _ => ψ.left) (𝟙 _)
    have hm : (𝟙 A.left : A.left ⟶ A.left) z ∈ P.U p ⊓ LB.wchart L (K := Unit) (fun _ => ψ.left)
      (fun _ => J (𝟙 _ ≫ ψ.left)) := ⟨hp, hm₂⟩
    have h1 := (map_sum _ _ _).symm.trans
      ((congrArg (germPull (𝟙 _) z _ hm) (h0 (p, fun _ => J (𝟙 _ ≫ ψ.left)))).trans (map_zero _))
    have h2 : (∑ k : Fin n, (κ.comp E.symm.toRingHom) (c k) * ρ (r j) ^ (k : ℕ)) *
        (sval (s i) f z J ^ t * gs (𝟙 _) z (P.U p) (ε.f p)) = 0 := by
      rw [Finset.sum_mul, ← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Eq.trans ?_ ((germPull_apply (𝟙 _) z _ hm _).trans (gs_mul (𝟙 _) z _ hm _ _)).symm
      refine Eq.trans ?_ (congrArg₂ (· * ·) (gs_appLE (𝟙 _) A.hom z ⊤ _ le_top hm (E.symm (c k)))
        ((gs_mul (𝟙 _) z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 _) z inf_le_left hm _)
          ((gs_res (𝟙 _) z inf_le_right hm _).trans (hσ k))))).symm
      have e₁ : (κ.comp E.symm.toRingHom) (c k) = gs (𝟙 _ ≫ A.hom) z ⊤ (E.symm (c k)) := by
        rw [Category.id_comp]
        exact germPull_apply _ _ _ _ _
      rw [e₁, e, mul_pow]
      conv_lhs => rw [← Nat.add_sub_of_le (k.2.le.trans hnt), pow_add]
      ring
    obtain ⟨a, ha⟩ := mem_range_of_sum_eq_zero (κ.comp E.symm.toRingHom) c hc (ρ (r j))
      ((mul_eq_zero.1 h2).resolve_right (mul_ne_zero (hy.pow _).ne_zero hεz))
    exact ⟨_, ha⟩
  have hall : ∀ a, ρ a ∈ κ.range := fun a => by
    obtain ⟨p, rfl⟩ := hsurj a
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.eval₂Hom_C]
      obtain ⟨c', rfl⟩ : ∃ c', ((⊤ : (Spec (CommRingCat.of K)).Opens).ι.appTop).hom c' = c :=
        have : IsIso (⊤ : (Spec (CommRingCat.of K)).Opens).ι :=
          inferInstanceAs (IsIso (Spec (CommRingCat.of K)).topIso.hom)
        (ConcreteCategory.bijective_of_isIso ((⊤ : (Spec (CommRingCat.of K)).Opens).ι.app ⊤)).2 c
      refine ⟨c', ?_⟩
      refine (germPull_apply _ _ _ _ _).trans (Eq.trans ?_ (germPull_apply _ _ _ _ _).symm)
      refine Eq.symm ((gs_appLE f _ z ⊤ _ le_top hi _).trans
        ((gs_pull _ (⊤ : (Spec (CommRingCat.of K)).Opens).ι z ⊤ trivial c').trans ?_))
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hf, Over.w]
    | add p p' h h' => rw [map_add (f := _), map_add (f := _)]; exact add_mem h h'
    | mul_X p j h => rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X']; exact mul_mem h (hrj j)
  obtain ⟨p, hp⟩ := exists_factor f w A.hom hk _ hD z hi (fun a => by
    obtain ⟨c, hc⟩ := hall a
    exact ⟨c, (germPull_apply _ _ _ _ _).symm.trans (hc.trans (germPull_apply _ _ _ _ _))⟩)
  rw [hf] at hp
  have h1 : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
  have h2 : η[A].left = p := by
    have := congrArg (fun x => x.left) (IsMonHom.one_hom ψ)
    simp only [Over.comp_left] at this
    rw [← this, hp, ← Category.assoc, h1]
    exact Category.id_comp _
  apply Over.OverMorphism.ext
  rw [hp, ← h2, Hom.one_def]
  simp

end GlobalTheory.AmpleRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidCube
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AmpleCube

open GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.CubeThm

section
attribute [local instance] CategoryTheory.Hom.group

variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]

theorem cube_pic_of_gen (L : LB B.left) (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen)
    (x y z : B ⟶ B) :
    GlobalTheory.CechPic.pull (x * y * z).left (GlobalTheory.CechPic.cls L hL) +
                 GlobalTheory.CechPic.pull x.left (GlobalTheory.CechPic.cls L hL) +
                 GlobalTheory.CechPic.pull y.left (GlobalTheory.CechPic.cls L hL) +
                 GlobalTheory.CechPic.pull z.left (GlobalTheory.CechPic.cls L hL) =
      GlobalTheory.CechPic.pull (x * y).left (GlobalTheory.CechPic.cls L hL) +
        GlobalTheory.CechPic.pull (x * z).left (GlobalTheory.CechPic.cls L hL) +
        GlobalTheory.CechPic.pull (y * z).left (GlobalTheory.CechPic.cls L hL) +
        GlobalTheory.CechPic.pull (1 : B ⟶ B).left (GlobalTheory.CechPic.cls L hL) := by
  set c := GlobalTheory.CechPic.cls L hL
  have hT : (Theta B L).IsLB := LB.isLB_linComb hL _ _
  have h0 : GlobalTheory.CechPic.cls (Theta B L) hT = 0 := (GlobalTheory.CechPic.cls_eq_zero_iff hT).2 hΘ
  have h1 : (∑ I : ULift.{0} (Finset (Fin 3)),
      ((-1 : ℤ) ^ (3 - I.down.card)) • GlobalTheory.CechPic.pull (psum B (x3 B) I.down).left c) = 0 :=
    (GlobalTheory.CechPic.cls_linComb hL (fun I : ULift.{0} (Finset (Fin 3)) => (psum B (x3 B) I.down).left)
      (fun I => (-1 : ℤ) ^ (3 - I.down.card)) hT).symm.trans h0
  have h2 := congrArg (GlobalTheory.CechPic.pull (lift x (lift y z)).left) h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at h2
  simp only [map_zsmul, ← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, comp_psum, lift_comp_cubeCoordinates] at h2
  rw [← Equiv.ulift.symm.sum_comp] at h2
  simp only [Equiv.ulift_symm_down] at h2
  rw [show (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide] at h2
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at h2
  have e0 : psum B ![x, y, z] ∅ = 1 := rfl
  have e1 : psum B ![x, y, z] {0} = x := (show _ = x * 1 from rfl).trans (mul_one x)
  have e2 : psum B ![x, y, z] {1} = y := (show _ = y * 1 from rfl).trans (mul_one y)
  have e3 : psum B ![x, y, z] {2} = z := (show _ = z * 1 from rfl).trans (mul_one z)
  have e4 : psum B ![x, y, z] {0, 1} = x * y :=
    (show _ = x * (y * 1) from rfl).trans (congrArg (x * ·) (mul_one y))
  have e5 : psum B ![x, y, z] {0, 2} = x * z :=
    (show _ = x * (z * 1) from rfl).trans (congrArg (x * ·) (mul_one z))
  have e6 : psum B ![x, y, z] {1, 2} = y * z :=
    (show _ = y * (z * 1) from rfl).trans (congrArg (y * ·) (mul_one z))
  have e7 : psum B ![x, y, z] {0, 1, 2} = x * y * z :=
    (show _ = x * (y * (z * 1)) from rfl).trans
      ((congrArg (x * ·) (congrArg (y * ·) (mul_one z))).trans (mul_assoc x y z).symm)
  rw [e0, e1, e2, e3, e4, e5, e6, e7] at h2
  have c0 : (∅ : Finset (Fin 3)).card = 0 := rfl
  have c1 : ({0} : Finset (Fin 3)).card = 1 := rfl
  have c2 : ({1} : Finset (Fin 3)).card = 1 := rfl
  have c3 : ({2} : Finset (Fin 3)).card = 1 := rfl
  have c4 : ({0, 1} : Finset (Fin 3)).card = 2 := rfl
  have c5 : ({0, 2} : Finset (Fin 3)).card = 2 := rfl
  have c6 : ({1, 2} : Finset (Fin 3)).card = 2 := rfl
  have c7 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := rfl
  rw [c0, c1, c2, c3, c4, c5, c6, c7] at h2
  norm_num at h2
  rw [← sub_eq_zero]
  rw [← h2]
  abel

end

theorem cubeSt : CubeSt := by
  intro K _ _ A _ _ hA L hL hamp c x y z
  obtain ⟨M, hM, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  exact cube_pic_of_gen A M hM (GlobalTheory.exists_gen_theta_of_isAbelianScheme K A hA M hM) x y z

end GlobalTheory.AmpleCube
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidFiniteOrder
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleFiniteOrder

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem two_smul_pow {G M : Type*} [Group G] [AddCommGroup M] (q : G → M) (q1 : q 1 = 0)
    (hq : ∀ x y : G, q (x * y) + q (x * y⁻¹) = q x + q x + q y + q y⁻¹) (ψ : G) (n : ℕ) :
    (2 : ℤ) • q (ψ ^ n) = ((n : ℤ) * (n + 1)) • q ψ + ((n : ℤ) * (n - 1)) • q ψ⁻¹ := by
  induction n using Nat.twoStepInduction with
  | zero => simp [q1]
  | one => simp [two_zsmul]
  | more n h0 h1 =>
    have h := hq (ψ ^ (n + 1)) ψ
    rw [← pow_succ, pow_succ ψ n, mul_inv_cancel_right, ← pow_succ] at h
    push_cast at h1 ⊢
    linear_combination (norm := module) (2 : ℤ) • h - h0 + (2 : ℤ) • h1

theorem pull_one_eq_zero {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (c : Pic A.left) :
    pull (1 : A ⟶ A).left c = 0 := by
  have h0 : pull (η[A]).left c = 0 := GlobalTheory.cechPic_sp_field_eq_zero K _
  rw [Hom.one_def, Over.comp_left, pull_comp, h0, map_zero]

theorem pull_iter {S : Scheme.{0}} {A : Over S} (σ : A ≅ A) (c : Pic A.left)
    (h : pull σ.hom.left c = c) (m : ℕ) : pull (GlobalTheory.SerreField.iter σ m).hom.left c = c := by
  induction m with
  | zero => exact pull_id c
  | succ m ih =>
    change pull ((GlobalTheory.SerreField.iter σ m).hom.left ≫ σ.hom.left) c = c
    rw [pull_comp, h, ih]

theorem eff_add_nsmul {X : Scheme.{0}} [IsIntegral X] {a b : Pic X} (ha : Eff a) (hb : Eff b) (k : ℕ) :
    Eff (a + k • b) := by
  induction k with
  | zero => simpa using ha
  | succ k ih => rw [succ_nsmul, ← add_assoc]; exact eff_add _ _ ih hb

theorem exists_ge_cast_ne_zero (K : Type) [Field K] (t : ℕ) : ∃ n : ℕ, t ≤ n ∧ (n : K) ≠ 0 := by
  by_cases h : (t : K) = 0
  · exact ⟨t + 1, by omega, by simp [h]⟩
  · exact ⟨t, le_rfl, h⟩

theorem finiteOrder_of_const_of_cube :
    GlobalTheory.AmpleRigid.ConstSt → GlobalTheory.AmpleRigid.CubeSt → GlobalTheory.AmpleRigid.FiniteOrderSt := by
  intro hConst hCube K _ _ A _ _ hA L hL hAmp σ hσ hfix
  haveI : IsIntegral A.left := GlobalTheory.SS.isIntegral_of_abelian A hA
  let q : (A ⟶ A) → Pic A.left := fun u => pull u.left (cls L hL)
  have q1 : q 1 = 0 := pull_one_eq_zero A _
  have hq : ∀ x y : A ⟶ A, q (x * y) + q (x * y⁻¹) = q x + q x + q y + q y⁻¹ := by
    intro x y
    have h : q (x * y * y⁻¹) + q x + q y + q y⁻¹ = q (x * y) + q (x * y⁻¹) + q (y * y⁻¹) + q 1 :=
      hCube K A hA L hL hAmp (cls L hL) x y y⁻¹
    rw [mul_inv_cancel_right, mul_inv_cancel, q1, add_zero, add_zero] at h
    exact h.symm
  obtain ⟨d, hd, r, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K A L hL).1 hAmp
  have heff : ∀ u : A ⟶ A, Eff ((d : ℤ) • q u) := fun u => by
    have h := eff_pull_of_veryAmpleBy K A.hom _ r s (GlobalTheory.AbLaw.isLB_pw hL d) hs u.left inferInstance
    rwa [cls_pw hL, map_zsmul] at h
  obtain ⟨t₀, ht₀⟩ := hConst K A hA L hL hAmp
    ((2 * d : ℤ) • (q (𝟙 A) + q (𝟙 A) + q (𝟙 A) + q (𝟙 A)⁻¹))
  obtain ⟨n, hn, hnK⟩ := exists_ge_cast_ne_zero K t₀
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hnK)
  obtain ⟨hfin, hdiv⟩ := GlobalTheory.TorsionDivisible.finite_torsion_and_divisible K A hA (k + 1) hnK
  obtain ⟨m, hm0, hm⟩ := GlobalTheory.SerreField.exists_iter_fix σ (𝟙_ (Over (Sp K))) (k + 1)
  refine ⟨m, hm0, ?_⟩
  have hx : q (GlobalTheory.SerreField.iter σ m).hom = q (𝟙 A) := (pull_iter σ _ hfix m).trans (pull_id _).symm
  have hxm : IsMonHom (GlobalTheory.SerreField.iter σ m).hom := inferInstance
  generalize (GlobalTheory.SerreField.iter σ m).hom = x at hm hx hxm ⊢
  have hu : IsMonHom (x * (𝟙 A)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  obtain ⟨ψ, hψ, e⟩ := hdiv _ hu (fun y hy => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hm y hy, Category.comp_id, mul_inv_cancel])
  have h1 := hq x (𝟙 A)
  rw [hx, e] at h1
  have h2 := two_smul_pow q q1 hq ψ (k + 1)
  have hψ1 : ψ = 1 := by
    refine ht₀ (d * ((k + 1) * (k + 2))) (hn.trans ?_) ψ hψ ?_
    · nlinarith [Nat.zero_le k, Nat.mul_le_mul_right ((k + 1) * (k + 2)) hd]
    · have h3 := eff_add_nsmul (eff_add _ _ (heff (x * 𝟙 A)) (heff (x * 𝟙 A))) (heff ψ⁻¹) ((k + 1) * k)
      convert h3 using 1
      change _ - _ • q ψ = _
      rw [← natCast_zsmul, ← natCast_zsmul]
      push_cast at h2 ⊢
      linear_combination (norm := module) (d : ℤ) • h2 - (2 * d : ℤ) • h1
  rw [hψ1, one_pow] at e
  exact mul_inv_eq_one.1 e

end GlobalTheory.AmpleFiniteOrder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidSerreAmple
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleRigid


open GlobalTheory.SerreField in
theorem serreAmple_of_finiteOrder_of_separated :
    FiniteOrderSt → SeparatedSt → SerreAmpleSt := by
  intro hfin hsep K _ _ A _ _ hA L hL hamp N hN3 hNK σ hσ hpull hfix
  haveI := hσ
  obtain ⟨m, hm0, hord⟩ := hfin K A hA L hL hamp σ hσ hpull
  have hFS : ∀ n : ℕ, 1 ≤ n → Flat (Out.mulA A n).left ∧ Surjective (Out.mulA A n).left :=
    fun n hn => flat_and_surjective_of_isFinite_abelianEnd
      forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K A hA _
      (GlobalTheory.AbLaw.MulN.isMonHom_mulA A n) (GlobalTheory.MulFiniteAny.isFinite_mulA K A hA n hn)
  have hu : IsMonHom (σ.hom * (𝟙 A)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  obtain ⟨-, hdiv⟩ := GlobalTheory.TorsionDivisible.finite_torsion_and_divisible K A hA N hNK
  obtain ⟨φ, hφ, e⟩ := hdiv (σ.hom * (𝟙 A)⁻¹) hu (fun x hx => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hfix K (𝟙 _) x hx, Category.comp_id, mul_inv_cancel])
  haveI := hφ
  have key : toRing σ.hom = 1 := by
    refine GlobalTheory.eq_one_of_pow_eq_one_of_congr_one (homRing A) N hN3 ?_ ?_ (toRing σ.hom) (toRing φ) m
      hm0 ?_ ?_
    · rintro k ⟨f, u, hu, hf⟩ hk h
      have h1 := congrArg (fun g : homRing A => g.1 (Additive.ofMul (𝟙 A))) h
      simp only [natCast_mul_apply, hf, Category.id_comp] at h1
      have h2 : u ^ k = 1 := h1
      have h3 : u = 1 := by
        obtain ⟨_, _⟩ := hFS k (by omega)
        haveI : Epi (Out.mulA A k).left := Flat.epi_of_flat_of_surjective _
        refine Over.OverMorphism.ext ((cancel_epi (Out.mulA A k).left).1 ?_)
        rw [← Over.comp_left, ← Over.comp_left, MonObj.comp_one, Out.mulA, MonObj.pow_comp,
          Category.id_comp, h2]
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · rintro q ⟨f, u, hu, hf⟩ hq h
      have h3 : u = 1 := hsep K A hA L hL hamp q hq u fun k => by
        obtain ⟨⟨g, v, hv, hg⟩, e⟩ := h k
        refine ⟨v, hv, ?_⟩
        have h1 := congrArg (fun g : homRing A => g.1 (Additive.ofMul (𝟙 A))) e
        simp only [← Nat.cast_pow, natCast_mul_apply, hf, hg, Category.id_comp] at h1
        exact h1
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · refine homRing_ext ?_
      change _ = Additive.ofMul (𝟙 A) + ((N : homRing A) * toRing φ).1 _
      rw [natCast_mul_apply, toRing_apply, toRing_apply, Category.id_comp, Category.id_comp,
        ← ofMul_pow, ← e, ← ofMul_mul, mul_comm, inv_mul_cancel_right]
    · rw [toRing_pow]
      exact homRing_ext (by rw [toRing_apply, hord, Category.id_comp]; rfl)
  have h1 := congrArg (fun g : homRing A => g.1 (Additive.ofMul (𝟙 A))) key
  simp only [toRing_apply, Category.id_comp] at h1
  exact h1

end GlobalTheory.AmpleRigid
end
end

