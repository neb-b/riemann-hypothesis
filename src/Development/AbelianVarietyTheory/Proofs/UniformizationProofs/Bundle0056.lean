module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionOverZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.GtCount

open GlobalTheory.TorusExt


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.GtCount.card_torsion_eq_mul {G B : Type} [AddCommGroup G] [AddCommGroup B] (p : G →+ B) (n : ℕ)
    (h : ∀ b : B, n • b = 0 → ∃ g, p g = b ∧ n • g = 0) :
    Nat.card {g : G // n • g = 0} = Nat.card {b : B // n • b = 0} * Nat.card {g : G // n • g = 0 ∧ p g = 0} := by
  have h' : ∀ b : {b : B // n • b = 0}, ∃ g, p g = b ∧ n • g = 0 := fun b => h b b.2
  choose s hs using h'
  have hp : ∀ g : {g : G // n • g = 0}, n • p g = 0 := fun g => by
    rw [← map_nsmul, g.2, map_zero]
  have hsec : ∀ (b b' : {b : B // n • b = 0}), (b : B) = b' → s b = s b' := by
    rintro b b' hbb
    rw [Subtype.ext hbb]
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun g => (⟨p g, hp g⟩, ⟨g - s ⟨p g, hp g⟩, ?_, ?_⟩)
      invFun := fun x => ⟨s x.1 + x.2.1, by rw [nsmul_add, (hs _).2, x.2.2.1, add_zero]⟩
      left_inv := fun g => Subtype.ext (add_sub_cancel _ _)
      right_inv := fun x => ?_ }
  · rw [nsmul_sub, g.2, (hs _).2, sub_zero]
  · rw [map_sub, (hs _).1, sub_self]
  · have hx : p (s x.1 + x.2.1) = x.1 := by rw [map_add (f := _), (hs _).1, x.2.2.2, add_zero]
    refine Prod.ext (Subtype.ext hx) (Subtype.ext ?_)
    change s x.1 + x.2.1 - s ⟨p (s x.1 + x.2.1), _⟩ = x.2.1
    rw [hsec ⟨p (s x.1 + x.2.1), _⟩ x.1 hx, add_sub_cancel_left]


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.GtCount.card_torus_torsion (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : Type) [Field F]
    [IsAlgClosed F] (n : ℕ) (hn : (n : F) ≠ 0) :
    Nat.card {t : Multiplicative X →* Fˣ // t ^ n = 1} = n ^ Module.finrank ℤ X := by
  haveI : NeZero (n : F) := ⟨hn⟩
  haveI : NeZero n := ⟨by rintro rfl; simp at hn⟩
  have hroots : Nat.card (rootsOfUnity n F) = n := by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F n
    exact hζ.card_rootsOfUnity
  let b := Module.Free.chooseBasis ℤ X
  let e₁ : {t : Multiplicative X →* Fˣ // t ^ n = 1} ≃ (Multiplicative X →* rootsOfUnity n F) :=
    { toFun := fun t => (t.1).codRestrict (rootsOfUnity n F) fun x => by
        have := DFunLike.congr_fun t.2 x
        simpa [MonoidHom.pow_apply, mem_rootsOfUnity] using this
      invFun := fun s => ⟨(rootsOfUnity n F).subtype.comp s, by
        refine MonoidHom.ext fun x => ?_
        simpa [MonoidHom.pow_apply] using (mem_rootsOfUnity _ _).1 (s x).2⟩
      left_inv := fun t => Subtype.ext (MonoidHom.ext fun x => rfl)
      right_inv := fun s => MonoidHom.ext fun x => Subtype.ext rfl }
  let e := e₁.trans (MonoidHom.toAdditiveRight.trans
    ((addMonoidHomLequivInt ℤ).toEquiv.trans (b.constr ℤ).symm.toEquiv))
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_congr Additive.toMul, hroots,
    Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card]

attribute [local instance] gtGroup

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in
theorem _root_.GlobalTheory.GtCount.gtTors_iff {R : Type} [CommRing R] [IsDomain R] {D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (n : ℕ) (g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F) : _root_.GlobalTheory.UU.GtTors D n g ↔ n • g = 0 := by
  unfold _root_.GlobalTheory.UU.GtTors
  simp [_root_.GlobalTheory.TorusExt.isNsmul_iff_eq, _root_.GlobalTheory.TorusExt.isZero_iff_eq]


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in
theorem _root_.GlobalTheory.GtCount.card_torsion_over_zero {R : Type} [CommRing R] [IsDomain R] (D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] (n : ℕ) (hn : (n : F) ≠ 0) :
    Nat.card {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // n • g = 0 ∧ g.b = 1} = n ^ D.rank := by
  let φ := _root_.GlobalTheory.TorusExt.torusPt D F
  have hinj : Function.Injective φ := _root_.GlobalTheory.TorusExt.torusPt_injective
  let e : {t : Multiplicative D.X →* Fˣ // t ^ n = 1} → {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // n • g = 0 ∧ g.b = 1} :=
    fun t => ⟨φ (Additive.ofMul t.1), by
      rw [← map_nsmul, ← ofMul_pow, t.2, ofMul_one, map_zero], _root_.GlobalTheory.TorusExt.torusPt_b _⟩
  have he : Function.Bijective e := by
    refine ⟨fun t t' htt => Subtype.ext ?_, fun g => ?_⟩
    · exact Additive.ofMul.injective (hinj (congrArg Subtype.val htt))
    · obtain ⟨t, ht⟩ := _root_.GlobalTheory.TorusExt.exists_torusPt_eq g.2.2
      refine ⟨⟨t, ?_⟩, Subtype.ext ht.symm⟩
      apply Additive.ofMul.injective
      apply hinj
      rw [ofMul_pow, map_nsmul, ← ht, g.2.1, ofMul_one, map_zero]
  rw [← Nat.card_congr (Equiv.ofBijective e he), _root_.GlobalTheory.GtCount.card_torus_torsion D.X F n hn]


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in
theorem _root_.GlobalTheory.GtCount.card_gtTors : _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws → _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws2 → (∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), (N : F) ≠ 0 → Nat.card {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // _root_.GlobalTheory.UU.GtTors D N g} = N ^ (2 * D.P.g + D.rank) ∧ Nat.card {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // _root_.GlobalTheory.UU.GtTors D N g ∧ g.b = _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre.zeroF D F} = N ^ D.rank) := by
  intro hL _ R _ _ _ D F _ _ _ N hN
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hz : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre.zeroF D F = 1 := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre.zeroF; rfl
  have h0 : (0 : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F).b = 1 := by
    simpa using _root_.GlobalTheory.TorusExt.nsmul_b 0 (0 : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F)
  let p : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F →+ Additive (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F ⟶ D.P.A) :=
    { toFun := fun g => Additive.ofMul g.b
      map_zero' := by rw [h0]; rfl
      map_add' := fun g g' => by rw [_root_.GlobalTheory.TorusExt.add_b]; rfl }
  have hsurj : ∀ b : Additive (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F ⟶ D.P.A), N • b = 0 → ∃ g, p g = b ∧ N • g = 0 := by
    intro b hb
    obtain ⟨g, hgb, hg⟩ := _root_.GlobalTheory.TorusExt.exists_nsmul_eq_of_pow_eq hN0 (0 : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F) (b := Additive.toMul b)
      (by rw [h0]; exact hb)
    exact ⟨g, by simp [p, hgb], hg⟩
  have hB : Nat.card {b : Additive (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F ⟶ D.P.A) // N • b = 0} = N ^ (2 * D.P.g) := by
    have := (hL.mulN (Spec (CommRingCat.of R)) D.P N (Nat.one_le_iff_ne_zero.2 hN0)).2.2.2.2 F
      (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F).hom hN
    rw [← this]
    exact Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun b => Iff.rfl)
  simp only [_root_.GlobalTheory.GtCount.gtTors_iff, hz]
  refine ⟨?_, _root_.GlobalTheory.GtCount.card_torsion_over_zero D F N hN⟩
  rw [_root_.GlobalTheory.GtCount.card_torsion_eq_mul p N hsurj, hB, pow_add]
  congr 1
  rw [← _root_.GlobalTheory.GtCount.card_torsion_over_zero D F N hN]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [p])

end GlobalTheory.GtCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ChainVal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UU

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GtTors.base_pow {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g) : g.b ^ k = 1 := by
  obtain ⟨h, ⟨gs, h₀, hs, hl⟩, hz⟩ := hg
  have key : ∀ i (hi : i < k + 1), (gs ⟨i, hi⟩).b = g.b ^ i := by
    intro i
    induction i with
    | zero => exact fun _ => h₀.1
    | succ i ih =>
      exact fun hi => (hs ⟨i, by omega⟩).1.trans ((congrArg (· * g.b) (ih (by omega))).trans (pow_succ _ _).symm)
  have hl' : gs ⟨k, Nat.lt_succ_self k⟩ = h := hl
  rw [← key k (Nat.lt_succ_self k), hl']; exact hz.1

theorem GtTors.chain_val {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g) {T : Over (Spec (CommRingCat.of R))}
    (σ : T ⟶ TF (R := R) F) {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (mu : D.X) :
    1 * cubN (th D z J) k 1 (σ ≫ g.b) (cP D T mu) = val (g.s mu) σ.left z J ^ k := by
  obtain ⟨h, ⟨gs, h₀, hs, hl⟩, hz⟩ := hg
  have C : IsCub (cubV D.cub z J) := isCub_cubV D.cub hJ
  have key : ∀ i (hi : i < k + 1), (gs ⟨i, hi⟩).b = g.b ^ i ∧
      val ((gs ⟨i, hi⟩).s mu) σ.left z J * cubN (th D z J) i 1 (σ ≫ g.b) (cP D T mu) = val (g.s mu) σ.left z J ^ i := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨h₀.1, (_root_.mul_one _).trans ((val_corr hJ (h₀.2 mu) σ.left).trans
        ((val_one _).trans (pow_zero _).symm))⟩
    | succ i ih =>
      intro hi
      obtain ⟨b₁, v₁⟩ := ih (by omega)
      obtain ⟨b₂, v₂⟩ := hs ⟨i, by omega⟩
      refine ⟨b₂.trans ((congrArg (· * g.b) b₁).trans (pow_succ _ _).symm), ?_⟩
      have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub σ hJ _ _ _))).symm.trans
        ((val_corr hJ (v₂ mu) σ.left).trans (val_mul hJ _ _ _))
      have e₁ : σ ≫ (gs (Fin.castSucc ⟨i, by omega⟩)).b = 1 * (σ ≫ g.b) ^ i := by
        rw [_root_.one_mul]; exact (congrArg (σ ≫ ·) b₁).trans (map_pow (preHom σ) _ _)
      have e₂ : σ ≫ DegPre.cF D F mu = cP D T mu := comp_cP D σ mu
      rw [e₁, e₂, C.s01, C.s12] at e
      rw [cubN, Finset.prod_range_succ, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, pow_succ, ← v₁, cubN]
      exact (congrArg₂ (· * ·) e rfl).trans (mul_right_comm _ _ _)
  have hk := (key k (Nat.lt_succ_self k)).2
  have hl' : gs ⟨k, Nat.lt_succ_self k⟩ = h := hl
  rw [hl'] at hk
  rw [← hk]
  exact congrArg₂ (· * ·) ((val_corr hJ (hz.2 mu) σ.left).trans (val_one _)).symm rfl

theorem GtTors.val_phi (hG : GlobalFnsSt) {k : ℕ} {g : GtPtF D F} (hg : GtTors D k g)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))) (hw : w.IsGen) (α : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 α g.b) (DegPre.deltaε k))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w))
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val u ρ.left z J = uVal D F k α g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (g.s α) w) (ρ ≫ fst _ _).left z J :=
  (gen_u D F hG k α (α + 0) g.b (by rw [add_zero, hg.base_pow, _root_.mul_one]) _
    (mulGen_isGen _ _ _ _ _ _ _ (g.isGen α) hw) (fun U _ h => by
    refine (Fintype.prod_sum_type _).trans ?_
    rw [Fin.prod_univ_four, Fin.prod_univ_two]
    show h (cP D _ α * g.b).left ^ (-1 : ℤ) * h (cP D _ α).left ^ (1 : ℤ) * h g.b.left ^ (1 : ℤ) *
      h (1 : TF (R := R) F ⟶ D.P.A).left ^ (-1 : ℤ) *
      (h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h g.b.left ^ (-(k : ℤ))) = _
    simp only [zpow_neg, zpow_one, zpow_natCast]
    ac_rfl)).2 u hu hc T ρ z J hJ

theorem val_delta (hG : GlobalFnsSt) (k : ℕ) (α mu : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val u ρ.left z J = uVal D F k α (cP D _ mu) ρ z J *
      val (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (ρ ≫ fst _ _).left z J := by
  have z₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D F ≫ DegPre.prB D F = 1 := lift_snd _ _
  have z₃ : (DegPre.zF D F ≫ DegPre.trF D F mu) ≫ DegPre.prB D F = cP D _ mu := by
    rw [trF_eq, Category.assoc, tr_pr, MonObj.comp_mul, z₂, ← Category.assoc, z₁, Category.id_comp, _root_.one_mul]
  have H := gen_u D F hG k α (α + k • mu) (cP D _ mu) (by rw [cPoint_add, cPoint_nsmul])
    (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (pullGen_isGen _ _ _ _ hu _) (fun U _ h => by
      have p₃ := prod_fam D F (DegPre.zF D F) (α + k • mu) k h
      have p₄ := prod_fam D F (DegPre.zF D F ≫ DegPre.trF D F mu) α k h
      rw [z₂, _root_.mul_one] at p₃
      rw [z₃] at p₄
      simp only [Over.comp_left, Category.assoc] at p₄
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)) ?_
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
  rw [← trF_eq] at H
  exact H.2 u hu (corr_of_val D.P.isLB fun _ _ _ => rfl) T ρ z J hJ

theorem phi_comm : (GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (g : GtPtF D F), GtTors D N g → ∀ (α mu : D.X) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε N))) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F N α mu) (DegPre.deltaε N))) (p : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 α g.b) (DegPre.deltaε N))) (p' : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 (α + N • mu) g.b) (DegPre.deltaε N))), w.IsGen → u.IsGen → p.IsGen → p'.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ p (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w) → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ p' (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s (α + N • mu)) w) → ∀ z J, Good D.P.L z J → val p' (𝟙 _) z J * val u (DegPre.trPt D F g.b).left z J = val u (𝟙 _) z J * val p (DegPre.trF D F mu).left z J) := by
  intro hG R _ _ D F _ _ k g hg α mu w u p p' hw hu hp hp' hc hc' y J hJ
  have C : IsCub (th D (T := DegPre.BF D F) y J) := isCub_cubV D.cub hJ
  have hm : fst (TF (R := R) F) D.P.A ≫ cP D _ mu = cP D _ mu := comp_cP D _ mu
  have hy : (fst (TF (R := R) F) D.P.A ≫ g.b) ^ k = 1 :=
    (map_pow (preHom (fst (TF (R := R) F) D.P.A)) _ _).symm.trans
      ((congrArg (preHom (fst (TF (R := R) F) D.P.A)) hg.base_pow).trans (map_one _))
  have t₁ := gt_nsmul (fst (TF (R := R) F) D.P.A) hJ g α mu k
  have t₃ := hg.chain_val (fst (TF (R := R) F) D.P.A) hJ mu
  have key := C.comm k _ _ _ (DegPre.prB D F) _ _ _ 1 1 1 t₁ (by rw [hy, C.face₂]) t₃
  have e₁ := hg.val_phi hG w hw (α + k • mu) p' hp' hc' _ (𝟙 _) y J hJ
  have e₂ := hg.val_phi hG w hw α p hp hc _ (DegPre.trPt D F (cP D _ mu)) y J hJ
  have e₃ := val_delta hG k α mu u hu _ (𝟙 _) y J hJ
  have e₄ := val_delta hG k α mu u hu _ (DegPre.trPt D F g.b) y J hJ
  rw [Category.id_comp, Over.id_left, uVal_id, val_mul hJ, cPoint_add, cPoint_nsmul] at e₁
  rw [tr_fst, uVal_tr, val_mul hJ, hm] at e₂
  rw [Category.id_comp, Over.id_left, uVal_id, hm] at e₃
  rw [tr_fst, uVal_tr, hm] at e₄
  rw [hy, _root_.mul_one (cP D _ α)] at key
  refine (congrArg₂ (· * ·) e₁ e₄).trans (Eq.trans ?_ (congrArg₂ (· * ·) e₃
    ((congrArg (fun q : DegPre.BF D F ⟶ DegPre.BF D F => val p q.left y J) (trF_eq D F mu)).trans e₂)).symm)
  apply Additive.ofMul.injective
  have key' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at key' ⊢
  linear_combination (norm := abel) key'

end GlobalTheory.UU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactTermAfterTorsion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.ExactTerm
open TWM TWO

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem comp_generic_injective :
    Function.Injective fun q : (TO hϖ hv).left ⟶ D.toPre.P.A.left => (ιS hϖ hv).left ≫ q := fun f g h => by
  have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  have e : f ≫ D.toPre.P.A.hom = g ≫ D.toPre.P.A.hom := by
    obtain ⟨a, ha⟩ := Spec.map_surjective (R := CommRingCat.of V) (S := CommRingCat.of (Ov v)) (f ≫ D.toPre.P.A.hom)
    obtain ⟨b, hb⟩ := Spec.map_surjective (R := CommRingCat.of V) (S := CommRingCat.of (Ov v)) (g ≫ D.toPre.P.A.hom)
    have e₁ : a ≫ CommRingCat.ofHom (algebraMap (Ov v) F) = b ≫ CommRingCat.ofHom (algebraMap (Ov v) F) :=
      Spec.map_injective (by
        rw [Spec.map_comp, Spec.map_comp, ha, hb]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ D.toPre.P.A.hom) h).trans (Category.assoc _ _ _)))
    have e₂ : a = b := CommRingCat.hom_ext (RingHom.ext fun x => Subtype.ext
      (RingHom.congr_fun (congrArg CommRingCat.Hom.hom e₁) x))
    exact ha.symm.trans ((congrArg Spec.map e₂).trans hb)
  have hU : ValuativeCriterion.Uniqueness D.toPre.P.A.hom := IsSeparated.valuativeCriterion _
  let S : ValuativeCommSq D.toPre.P.A.hom :=
    { R := Ov v, K := F, i₁ := (ιS hϖ hv).left ≫ f, i₂ := f ≫ D.toPre.P.A.hom, commSq := ⟨Category.assoc _ _ _⟩ }
  exact congrArg CommSq.LiftStruct.l ((hU S).elim ⟨f, rfl, rfl⟩ ⟨g, h.symm, e.symm⟩)

theorem exists_unit_const {K : Type} [Fintype K] {φ : K → ((TO hϖ hv).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb D.toPre.P.L φ ε)) (ht : t.IsGen)
    (hf : ∀ (U : Type) [CommGroup U] (h : ((TF (R := V) F).left ⟶ D.toPre.P.A.left) → U),
      ∏ k, h ((ιS hϖ hv).left ≫ φ k) ^ ε k = 1) :
    ∃ u : F, v u = 0 ∧ ∀ z J, Good D.toPre.P.L z J → (val t (ιS hϖ hv).left z J).val = cst F z u := by
  have hI : IsIso (Scheme.Hom.appTop (𝟙 (TO hϖ hv).left)) :=
    inferInstanceAs (IsIso (Scheme.Hom.app (𝟙 (TO hϖ hv).left) ⊤))
  obtain ⟨a, ha⟩ := H1.exists_const D.toPre.P.L D.toPre.P.isLB (𝟙 _) (ConcreteCategory.bijective_of_isIso _).2 t ht
    (fun U _ h => by
      have := hf U (Function.extend (fun q => (ιS hϖ hv).left ≫ q) h 1)
      simpa only [(comp_generic_injective hϖ hv).extend_apply] using this)
  have hu : IsUnit a := (TO hϖ hv).left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' D.toPre.P.isLB y
    have q := ha _ (𝟙 _) y J hJ
    rw [Category.comp_id] at q
    exact (congrArg IsUnit (q.trans (gs_eq (𝟙 _) y ⊤ trivial a))).mp (Units.isUnit _)
  refine ⟨ιr (v := v) a, v_unit v (hu.map (Scheme.ΓSpecIso (CommRingCat.of (Ov v))).hom.hom).unit, fun z J hJ => ?_⟩
  rw [ha _ _ z J hJ, Category.comp_id, ← Category.id_comp (ιS hϖ hv).left]
  exact (gs_pull (𝟙 _) (ιS hϖ hv).left z ⊤ trivial a).symm.trans (congrArg (gs (𝟙 _) z ⊤) (appTop_specMap _ a))

theorem cst_gF {Z : Scheme.{0}} (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (c : V) :
    Geo.Tor.cst ((ρ ≫ (DegPre.prB D.toPre F).left) ≫ D.toPre.P.A.hom) z c = gs ρ z ⊤ (gF D.toPre F (algVF c)) := by
  have e : (ρ ≫ (DegPre.prB D.toPre F).left) ≫ D.toPre.P.A.hom =
      (ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) ≫ Spec.map (CommRingCat.ofHom (algVF (F := F) (V := V))) := by
    rw [← TF_hom, Category.assoc, Category.assoc, Over.w, Over.w]
  rw [e]
  refine (gs_pull _ _ z ⊤ trivial _).symm.trans (Eq.trans ?_ (gs_pull ρ _ z ⊤ trivial _).symm)
  refine congrArg (gs _ z ⊤) ((appTop_specMap _ _).trans ?_)
  simp


include hϖ hv in
theorem vge_iff {k : ℕ} {χ : D.toPre.X} (b : D.toPre.SecB k χ)
    (hb : ∀ σ : D.toPre.SecB k χ, ∃ c : V, ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J),
      Good D.toPre.P.L z J → sval σ r z J = Geo.Tor.cst (r ≫ D.toPre.P.A.hom) z c * sval b r z J)
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))) {r : ℚ} (hs : VGe D F v k χ s r) :
    ∃ a : F, (r : WithTop ℚ) ≤ v a ∧ (∀ r' : ℚ, (r' : WithTop ℚ) ≤ v a → VGe D F v k χ s r') ∧
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval s ρ z J = gs ρ z ⊤ (gF D.toPre F a) * sval b (ρ ≫ (DegPre.prB D.toPre F).left) z J := by
  have hL := D.toPre.P.isLB
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := hs
  choose c hc using fun i => hb (σ i)
  have key : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
      sval s ρ z J = gs ρ z ⊤ (gF D.toPre F (∑ i, a i * algVF (c i))) *
        sval b (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun Z ρ z J hJ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [SectionScalarValuation.sval_lin (fun i => gF D.toPre F (a i)) σF (fun j => hsum j) ρ z hJ, map_sum,
      SectionScalarValuation.gs_sum ρ z ⊤ trivial, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← SectionScalarValuation.secScal_sval (hscal i) ρ z hJ, hc i _ _ z J hJ, cst_gF, map_mul, gs_mul ρ z ⊤ trivial, _root_.mul_assoc]
  refine ⟨∑ i, a i * algVF (c i), AddValuation.map_le_sum v fun i _ => ?_, fun r' hr' => ?_, key⟩
  · rw [AddValuation.map_mul]
    exact le_add_of_le_of_nonneg (hva i) (v_of_V v hϖ hv (c i)).1
  · let bF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)) :=
      VVRank.pullTo b (DegPre.prB D.toPre F).left fun i => (GC.famφ_eq _ _ _ i).symm
    refine ⟨1, fun _ => _, fun _ => b, fun _ => bF, fun _ => SectionScalarValuation.secScal_of_sval hL fun y J hJ =>
      (VVRank.sval_pullTo _ _ _ _ y hJ).symm, fun _ => hr', fun j => ?_⟩
    rw [Fin.sum_univ_one]
    refine sec_ext_val hL (s' := SecOps.secScale (gF D.toPre F _) bF) (fun y J hJ => ?_) j
    have hm := hJ.mem (DegPre.famφ D.toPre F χ) (𝟙 _)
    exact (key _ _ y J hJ).trans ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) (gs_res _ y le_top hm _)
      (VVRank.sval_pullTo _ _ _ _ y hJ))).symm

theorem v_coef {χ : D.toPre.X} (b : D.toPre.SecB 1 χ) (s : Fam D.toPre F 1) (a : F)
    (hs : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval (s.s χ) ρ z J = gs ρ z ⊤ (gF D.toPre F a) * sval b (ρ ≫ (DegPre.prB D.toPre F).left) z J)
    (g : GtPtF D.toPre F) (m : TO hϖ hv ⟶ D.toPre.P.A) (hm : ιS hϖ hv ≫ m = g.b)
    (hu : ∀ z J, Good D.toPre.P.L z J → IsUnit (sval b (Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ m.left) z J))
    (w : Frm D.toPre F 1 g.b) (hw : w.IsGen) {l ω : ℚ} (hl : GenV hϖ hv (g.s χ) l) (hω : GenV hϖ hv w ω) :
    v (coef s g w χ) = v a + l + ω := by
  have hL := D.toPre.P.isLB
  obtain ⟨t₀, h₀, v₀⟩ := exists_gen_of_isUnit hL b m.left hu
  obtain ⟨φ₁, e₁, t₁, h₁, x₁, hx₁, v₁⟩ := hl
  obtain ⟨φ₂, e₂, t₂, h₂, x₂, hx₂, v₂⟩ := hω
  have hm' : (ιS hϖ hv).left ≫ m.left = g.b.left := congrArg (fun q => q.left) hm
  obtain ⟨u, hu₀, vu⟩ := exists_unit_const hϖ hv
    (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ t₀ t₁) t₂) (LB.invGen _ _ _
      (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig (TO hϖ hv).hom)))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ h₀ h₁) h₂)
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.rig_gen _))) (fun U _ h => by
      have p₀ := SectionScalarValuation.prod_famB D.toPre g.b χ 1 h
      have p₁ := prod_gt g.b χ h
      have p₂ := CoefBasic.prod_line 1 g.b h
      have p₃ : (ιS hϖ hv).left ≫ (TO hϖ hv).hom ≫ eSec D.toPre.P.A = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := by
        rw [← Category.assoc, Over.w]; rfl
      simp only [e₁] at p₁
      simp only [e₂] at p₂
      simp only [← hm', Category.assoc] at p₀
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, p₀, p₁, p₂, p₃]
      rw [mul_comm g.b, hm']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one, SectionScalarValuation.cQ, cP]
      module)
  have e : coef s g w χ = a * x₁ * x₂ * u := CoefBasic.coef_eq fun z J hJ => by
    have q := vu z J hJ
    rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, Over.w, Units.val_mul, Units.val_mul, Units.val_mul,
      v₀ _ _ z J hJ, hm', Units.mul_inv_eq_iff_eq_mul] at q
    replace q : _ = _ * (rigV D.toPre (TF (R := V) F).hom z J).val := q
    have q₁ : gs (lift (𝟙 (TF (R := V) F)) g.b).left z ⊤ (gF D.toPre F a) = cst F z a := by
      refine (gs_pull _ (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _).trans ?_
      rw [← Over.comp_left, lift_fst]; rfl
    rw [hs _ _ z J hJ, v₁ z J hJ, v₂ z J hJ, q₁, ← Over.comp_left, lift_snd, pow_one]
    simp only [CoefBasic.cst_eq, map_mul] at q ⊢
    exact Eq.symm (by linear_combination (CoefBasic.cstH z a * CoefBasic.cstH z x₁ * CoefBasic.cstH z x₂) * q)
  rw [e, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, hx₁, hx₂, hu₀, add_zero]

theorem exact_term_after_torsion : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ ϑ : Fam D.toPre F 1, Prim D Q v ϑ → ∀ (n : ℕ), 2 ≤ n → IsUnit (n : V) → ∀ (g : GtPtF D.toPre F) (χ : D.toPre.X), ∃ (h o g₂ : GtPtF D.toPre F), o.IsZero ∧ GtPtF.IsNsmul n h o ∧ g.IsAdd h g₂ ∧ ∀ (w : Frm D.toPre F 1 g₂.b) l ω, w.IsGen → GtV hϖ hv g₂ l → GenV hϖ hv w ω → v (coef ϑ g₂ w χ) = (((Q χ : ℚ) + l χ + ω : ℚ) : WithTop ℚ) := by
  intro hL _ _ _ _ V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv ϑ hϑ n hn hnV g χ
  obtain ⟨b, hb, hb'⟩ := exists_secB_good hL.1 D.toPre χ
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := vge_iff hϖ hv b hb (ϑ.s χ) (hϑ.1 χ)
  have ha : v a = ((Q χ : ℚ) : WithTop ℚ) := by
    simp only [Nat.cast_one, div_one, zero_add] at ha₁
    refine le_antisymm (not_lt.1 fun h => ?_) ha₁
    obtain ⟨q, hq₁, hq₂⟩ := WithTop.lt_iff_exists_coe_btwn.1 h
    refine hϑ.2 (q - Q χ) (sub_pos.2 (WithTop.coe_lt_coe.1 hq₁)) ((n1a V ϖ hϖ D Q hQ F v hv 1 le_rfl {χ}
      (fun χ' => ⟨χ, Finset.mem_singleton_self _, χ' - χ, by simp⟩) ϑ _).2 fun α hα => ?_)
    rw [Finset.mem_singleton] at hα
    subst hα
    refine ha₂ _ ?_
    simpa using hq₂.le
  have : IsAlgClosed (ResidueField (Ov v)) := isAlgClosed_residueField_of_valuationRing_of_isAlgClosed (Ov v) F
  obtain ⟨m, hm⟩ := exists_liftO hϖ hv g.b
  let ρ : Over.mk (Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ (TO hϖ hv).hom) ⟶ TO hϖ hv := Over.homMk _ rfl
  have hK : (n : ResidueField (Ov v)) ≠ 0 := by
    have := (hnV.map ((residue (Ov v)).comp (fO v hϖ hv))).ne_zero
    rwa [map_natCast] at this
  obtain ⟨x₀, hx₀, hu⟩ := hb' (ResidueField (Ov v)) _ n hn hK (ρ ≫ m)
  obtain ⟨hfin, hflat, -⟩ := hL.1.mulN _ D.toPre.P n (by omega)
  obtain ⟨x, hx, ex⟩ : ∃ x : TO hϖ hv ⟶ D.toPre.P.A, x ^ n = 1 ∧
      Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ x.left = x₀.left :=
    exists_torsion_lift (Ov v) D.toPre.P.A n (TO hϖ hv).hom x₀ hx₀
  have ex' : ρ ≫ x = x₀ := Over.OverMorphism.ext ex
  letI := TorusExt.gtGroup D.toPre F
  obtain ⟨h, hh₁, hh₂⟩ := TorusExt.exists_nsmul_eq_of_pow_eq (n := n) (by omega) (0 : GtPtF D.toPre F)
    (b := ιS hϖ hv ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one, TorusExt.zero_b])
  refine ⟨h, 0, g + h, (TorusExt.isZero_iff_eq _).2 rfl, (TorusExt.isNsmul_iff_eq _ _ _).2 hh₂.symm,
    (TorusExt.isAdd_iff_eq _ _ _).2 rfl, fun w l ω hw hl hω => ?_⟩
  rw [v_coef hϖ hv b ϑ a ha₃ (g + h) (m * x) (by rw [MonObj.comp_mul, hm, TorusExt.add_b, hh₁]) (fun z J hJ => by
    have q := hu z J hJ
    rw [← ex', ← MonObj.comp_mul] at q
    exact q) w hw (hl χ) hω, ha]
  rfl

end GlobalTheory.UT.ExactTerm
end
end

