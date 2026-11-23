module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBijectionRightInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveRegular
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.DblTransp

section Inv

open Filter
open scoped Classical

theorem isTame_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ A : Fn F n d →ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), A (e Φ) = Φ) → IsTame F A := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE hbij A hA g hg
  obtain ⟨m, c, φ, hφ, hstd, rfl⟩ := GlobalTheory.MixEvAdm.sb_decomp F (Fin n × Fin d) g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  have hbi : Function.Bijective ei :=
    ⟨GlobalTheory.T.weil_eigen_injective_extends F E σ B n d X W M M₁ hP.good e hbij.injOn ei ev (fun v => (hev v).1) hloc,
      GlobalTheory.T.weil_eigen_surjective_extends F E σ B n d X W M M₁ hP.good hM₁ e hbij.surjOn ei ev hev hloc⟩
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.FrechetOpenMapping.schwartz_exists_inverse _ _ ei hbi
  have hpre : ∀ j v, ∃ ψ ∈ SB (Fin n × Fin d → Fv F v), ev v ψ = φ j v ∧ (φ j v = M₁.vac v → ψ = M.vac v) := by
    intro j v
    by_cases h : φ j v = M₁.vac v
    · exact ⟨M.vac v, (hP.good.vac v).1, (hev v).1.trans h.symm, fun _ => rfl⟩
    · have h2 : φ j v ∈ (SB (Fin n × Fin d → Fv F v)).map (ev v) := (hev v).2.symm ▸ hφ j v
      obtain ⟨ψ, hψ, hψe⟩ := Submodule.mem_map.1 h2
      exact ⟨ψ, hψ, hψe, fun h' => (h h').elim⟩
  choose ψ hψSB hψev hψvac using hpre
  have hψfam : ∀ j, ∀ᶠ v in cofinite, ψ j v = M.vac v := fun j =>
    ((hstd j).and hM₁.std).mono fun v hv => hψvac j v (hv.1.trans hv.2.symm)
  have hψstd : ∀ j, ∀ᶠ v in cofinite,
      ψ j v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun j =>
    ((hψfam j).and hP.good.std).mono fun v hv => hv.1.trans hv.2
  have hG : ∀ j, (fun y : Fin n × Fin d → Af F => ∏ᶠ v, ψ j v fun i => evalV F v (y i)) ∈
      SB (Fin n × Fin d → Af F) := fun j =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB j) (hψstd j),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB j) (hψstd j)⟩
  refine ⟨Fin m, inferInstance, fun j => c j • S, fun j y => ∏ᶠ v, ψ j v fun i => evalV F v (y i), hG, fun f => ?_⟩
  have hsplit : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
      (∑ j, c j • fun y => ∏ᶠ v, φ j v fun i => evalV F v (y i)) =
      ∑ j, c j • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) := by
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm]
    rfl
  have hφe : ∀ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ j) =
      e (pureA F ((S f : SInf F _) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
        (fun y => ∏ᶠ v, ψ j v fun i => evalV F v (y i))) := by
    intro j
    have h1 := hloc (S f) (ψ j) (hψSB j) (hψfam j)
    rw [hS] at h1
    have h2 : (fun v => ev v (ψ j v)) = φ j := funext fun v => hψev j v
    rw [h2] at h1
    exact h1.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsplit, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hφe j, hA _ (Submodule.subset_span ⟨S f, _, hG j, rfl⟩)]
  funext x
  simp [pureA, mul_assoc]

end Inv

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ T : Fn F n d ≃ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ = e Φ) →
    ∀ d' d₁' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) → (∀ x : Matrix (Fin n) (Fin d) (AE F E), d₁'.e xᵀ = M₁.co.e x) →
      HasDbl (cA σ) (adeleClass F) B.ψ (-1) (incM F W.J) (incM F X.J) d' d₁' T := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe d' d₁' hd' hd₁'
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hTs : ∀ x, x ∈ schA F (Fin n × Fin d) ↔ T x ∈ schA F (Fin n × Fin d) := fun x => by
    constructor
    · intro hx
      rw [hTe x hx]
      exact hbij.mapsTo hx
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hbij.surjOn hx
      have : T y = T x := by rw [hTe y hy, hyx]
      rw [← T.injective this]
      exact hy
  have hgood : IsGoodInt (adeleClass F) B.ψ d' d₁' T := by
    refine ⟨hTs, fun w Φ hΦ => ?_, fun l => ?_, fun μ hμ => ?_⟩
    · have e1 : d'.e w = M.co.e wᵀ := by rw [← hd', Matrix.transpose_transpose]
      have e2 : d₁'.e w = M₁.co.e wᵀ := by rw [← hd₁', Matrix.transpose_transpose]
      have r1 : d'.rho B.ψ w = M.co.rho B.ψ wᵀ := by unfold Darboux.rho; rw [e1]
      have r2 : d₁'.rho B.ψ w = M₁.co.rho B.ψ wᵀ := by unfold Darboux.rho; rw [e2]
      have hm : M.co.rho B.ψ wᵀ Φ ∈ schA F (Fin n × Fin d) :=
        _root_.GlobalTheory.SchrKeepsSchA.schr_mem_schA F B.ψ hpair.base.std _ (M.co.e wᵀ) Φ hΦ
      have := hev.Heisenberg₂ wᵀ Φ hΦ
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at this
      rw [r1, r2, hTe _ hm, hTe _ hΦ, this]
    · refine (_root_.GlobalTheory.ModelAdmUnconditional.model_admissible_iff_evaluation F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij l).trans
        (GlobalTheory.DblInt.adm_congr ?_)
      intro Φ hΦ
      simp [hTe Φ hΦ]
    · obtain ⟨c, hc⟩ := _root_.GlobalTheory.EvalUnitUnconditional.exists_const F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij μ hμ
      exact ⟨c, fun Φ hΦ => by rw [hTe Φ hΦ]; exact hc Φ hΦ⟩
  have ht : IsTame F T.toLinearMap := by
    intro g hg
    obtain ⟨ι, inst, P, g', hg', hPe⟩ := GlobalTheory.EvTame.isTame_of_isEv F E σ B n d n d X W X W M M₁ 1 1 ∅ e hpair.good hM₁ hev g hg
    refine ⟨ι, inst, P, g', hg', fun f => ?_⟩
    rw [← hPe f]
    exact hTe _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)
  have hti : IsTame F T.symm.toLinearMap :=
    isTame_inv F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T.symm.toLinearMap
      (fun Φ hΦ => by rw [← hTe Φ hΦ]; simp)
  exact GlobalTheory.DblInt.hasDbl_of_tame (cA σ) B.ψ (GlobalTheory.StdCharFromIsStd.norm_psi hpair.base.std) (-1) _ _ d' d₁' T hgood ht hti

end GlobalTheory.DblTransp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingConditionLocusIsClopen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.HTWeilLocus

open GlobalTheory.CechPic GlobalTheory.DiagPairing

section Root

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_weilIs_root {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (M : ℕ) (T : Over S) (x y : T ⟶ o.A) (hM : 0 < M)
    (hx : x ^ M = 1) (hy : y ^ M = 1) :
    ∃ c₀ : Γ(T.left, ⊤)ˣ, c₀ ^ M = 1 ∧ Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M x y c₀ := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ o.A), pc o.isLB (x * x') y = pc o.isLB x y + pc o.isLB x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ o.A), pc o.isLB x (y * y') = pc o.isLB x y + pc o.isLB x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ z : T ⟶ o.A, z ^ M = 1 → ∀ q : T.left, ∃ V : T.left.Opens, q ∈ V ∧
      ∃ θ : Out.ThetaGrp o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M (Out.overRes V),
        θ.pt = Out.overResι V ≫ z := fun z hz q => by
    obtain ⟨θ, hθ⟩ := exists_theta_diag o.isLB hB hB' (k := M) (Out.overResι ⊤ ≫ z)
      (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
    exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG o.ab hD (lifts x hx) (lifts y hy)
  obtain ⟨c₁, hc₁⟩ := CommutatorPairing.exists_weilIs hG o.ab hD (lifts 1 (one_pow M)) (lifts y hy)
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG o.ab hD hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ * c₁ = c₁ := CommutatorPairing.weilIs_unique hG o.ab hD h11 hc₁
  have e₁' : c₁ = 1 := mul_eq_left.1 e₁
  have pw : ∀ m : ℕ, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M (x ^ (m + 1)) y (c₀ ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hc₀
    | succ m ih =>
      rw [pow_succ x (m + 1), pow_succ c₀ (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG o.ab hD ih hc₀
  have hp := pw (M - 1)
  rw [Nat.sub_add_cancel hM, hx] at hp
  exact ⟨c₀, CommutatorPairing.weilIs_unique hG o.ab hD hp (e₁' ▸ hc₁), hc₀⟩

end Root

end GlobalTheory.HTWeilLocus

namespace GlobalTheory.HTWeilLocus

open GlobalTheory.LevCover

theorem weil_locus_clopen : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Z : Over S) (t₁ : Z.left ⟶ Sp (cycAway M)) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ (β : cycAway M →+* k) (z : kˣ), x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) → ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e c) (unitOn (z ^ (2 * omegaStd a c)))) := by
  intro p _ D R _ b N h M hM hMp S t o Z t₁ e hadd hpow
  have hG : Out.GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hLB : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hMZ : IsUnit (M : Γ(Z.left, ⊤)) := by
    have := (b.unit M hMp).map (fnOn (Z.hom ≫ t))
    rwa [map_natCast] at this
  let ζu : (cycAway M)ˣ := Units.ofPowEqOne (zetaAway M) M (zetaAway_pow_self M hM.ne') hM.ne'
  have hζv : (ζu : cycAway M) = zetaAway M := Units.val_ofPowEqOne _ _ _ _
  have hζM : ∀ (k : Type) [Field k] (β : cycAway M →+* k), Units.map β.toMonoidHom ζu ^ M = 1 := fun k _ β => by
    rw [← map_pow, Units.pow_ofPowEqOne, map_one]
  let P2 : (Fin h ⊕ Fin h → ℤ) → (Fin h ⊕ Fin h → ℤ) → HkClopen.GeoCond Z.left := fun a c k _ _ x =>
    ∀ (β : cycAway M →+* k) (z : kˣ), x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) →
      Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a)
        ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e c) (unitOn (z ^ (2 * omegaStd a c)))
  have locPair : ∀ a c, HkClopen.Loc (P2 a c) := fun a c => by
    obtain ⟨v, hv, hW⟩ := exists_weilIs_root o M Z (e a) (e c) hM (hpow a) (hpow c)
    refine (GlobalTheory.loc_units_eq Z.left M v (Units.map (fnOn t₁).toMonoidHom (ζu ^ (2 * omegaStd a c))) hMZ hv
      fun k _ _ g => ?_).congr fun k _ _ g => ?_
    · obtain ⟨β, hβ⟩ := exists_spMap (g ≫ t₁)
      rw [map_fnOn _ g β hβ, ← GlobalTheory.SiegCover.unitOn_pow', map_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hζM, one_zpow]
      exact GlobalTheory.SiegCover.unitOn_one'
    · have hW' := GlobalTheory.CommPairing.weilIs_pull hG o.ab hLB (Over.homMk g rfl : Over.mk (g ≫ Z.hom) ⟶ Z) hW
      obtain ⟨β, hβ⟩ := exists_spMap (g ≫ t₁)
      have hu := map_fnOn _ g β hβ (ζu ^ (2 * omegaStd a c))
      rw [show Units.map β.toMonoidHom (ζu ^ (2 * omegaStd a c)) =
        Units.map β.toMonoidHom ζu ^ (2 * omegaStd a c) from map_zpow _ _ _] at hu
      have hzβ : ((Units.map β.toMonoidHom ζu : kˣ) : k) = β (zetaAway M) := by
        rw [Units.coe_map]; exact congrArg β hζv
      constructor
      · intro E β' z hβ' hz
        obtain rfl : β = β' := spMap_inj' (hβ.symm.trans hβ')
        obtain rfl : z = Units.map β.toMonoidHom ζu := Units.ext (hz.trans hzβ.symm)
        rw [← hu, ← E]
        exact hW'
      · intro H
        exact GlobalTheory.CommutatorPairing.weilIs_unique hG o.ab hLB hW' (hu ▸ H β _ hβ hzβ)
  have e1 : ∀ a c, e (a + M • c) = e a := fun a c => by
    rw [hadd, add_map_nsmul hadd, hpow, _root_.mul_one]
  have inv : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ Z.left) (a a' c₁ c₂ : Fin h ⊕ Fin h → ℤ),
      P2 a a' k g → P2 (a + M • c₁) (a' + M • c₂) k g := by
    intro k _ _ g a a' c₁ c₂ H β z hβ hz
    rw [e1, e1]
    have hzM : z ^ M = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, hz, ← map_pow, zetaAway_pow_self M hM.ne', map_one, Units.val_one])
    obtain ⟨m, hm⟩ : ∃ m : ℤ, omegaStd (a + M • c₁) (a' + M • c₂) = omegaStd a a' + M * m :=
      ⟨_, GlobalTheory.SiegCover.omegaStd_add_nsmul M a a' c₁ c₂⟩
    have hz' : z ^ (2 * omegaStd (a + M • c₁) (a' + M • c₂)) = z ^ (2 * omegaStd a a') := by
      rw [hm, mul_add, zpow_add, show (2 : ℤ) * (M * m) = M * (2 * m) by ring, zpow_mul _ (M : ℤ), zpow_natCast,
        hzM, one_zpow, _root_.mul_one]
    rw [hz']
    exact H β z hβ hz
  obtain ⟨κ, hκ, q, hq⟩ := exists_finite_mod (Fin h ⊕ Fin h → ℤ) hM
  haveI := hκ
  let r : κ → (Fin h ⊕ Fin h → ℤ) := Function.invFun q
  have localization₂ : HkClopen.Loc (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ Z.left) => ∀ a a', P2 a a' k g) := by
    refine (HkClopen.Loc.all (I₀ := κ × κ) (P := fun i => P2 (r i.1) (r i.2)) fun i => locPair _ _).congr
      fun k _ _ g => ⟨fun H a a' => ?_, fun H i => H _ _⟩
    obtain ⟨c₁, e₁⟩ := hq (r (q a)) a (Function.invFun_eq ⟨a, rfl⟩)
    obtain ⟨c₂, e₂⟩ := hq (r (q a')) a' (Function.invFun_eq ⟨a', rfl⟩)
    rw [e₁, e₂]
    exact inv k g _ _ c₁ c₂ (H (q a, q a'))
  exact localization₂.congr fun k _ _ x =>
    ⟨fun H β z hβ hz a c => H a c β z hβ hz, fun H a c β z hβ hz => H β z hβ hz a c⟩

end GlobalTheory.HTWeilLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtChar
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSum

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}


open Classical in
def base (X₁ : Setup F W i) (z₁ : X₁.M.Z) : X₁.S.Gam :=
  if h : (X₁.S.supI X₁.M z₁).Nonempty then h.some else 0

def wtChar (D : Deep X₁ ε₁) (T : AddSubgroup D.X.S.Gam) (a : D.X.S.Gam) : T →+ ZMod D.X.S.N where
  toFun t := ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N) (eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a))
  map_zero' := by simp [eStd]
  map_add' := by
    intro s t
    rw [← map_add (f := _)]
    congr 1
    simp only [eStd, AddSubgroup.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring


open Classical in
def lift (D : Deep X₁ ε₁) (z₂ : D.X.M.Z) (κ : X₁.S.Gam) : D.X.S.Gam :=
  if h : ∃ h' ∈ D.X.S.HH D.X.M z₂, D.m • h' = D.lab κ then h.choose else 0

def part (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z) (a : D.X.S.Gam) (κ : X₁.S.HH X₁.M z₁) : D.X.Ω₁ :=
  (∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj (D.X.S.TT D.X.M z₂) (wtChar D _ a) j D.X.ρ.i₀) *
      D.X.S.ev (lift D z₂ (κ : X₁.S.Gam)) j) / D.X.S.th (D.lab (base X₁ z₁))

end GlobalTheory.Poinc.GSum
end
end

