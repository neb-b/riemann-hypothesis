module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasChartsOfForallIsAffineOpen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIndexOfLocal
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (LBIso)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetSer

theorem exists_index_of_local {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    (e : Spec (CommRingCat.of R) ⟶ X) : ∃ j : L.ι, ⊤ ≤ e ⁻¹ᵁ L.U j := by
  have h : e (IsLocalRing.closedPoint R) ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨j, (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of R) e hj).ge⟩

end GlobalTheory.JetSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsToJetEq
section
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart
namespace GlobalTheory.JetSer
variable {R : Type} [CommRing R] {κ : Type}

theorem jet_mk_eq_iff (m : ℕ) (P Q : MvPolynomial κ R) :
    (Ideal.Quotient.mk _ P : JetR R κ m) = Ideal.Quotient.mk _ Q ↔
      ∀ e : κ →₀ ℕ, Finsupp.degree e < m + 1 → P.coeff e = Q.coeff e := by
  rw [Ideal.Quotient.eq]
  refine (MvPolynomial.mem_pow_idealOfVars_iff' (m + 1) (P - Q)).trans ?_
  simp only [MvPolynomial.coeff_sub, sub_eq_zero]

variable [Finite κ]

theorem toJet_eq_mk_iff (m : ℕ) (g : MvPowerSeries κ R) (Q : MvPolynomial κ R) :
    toJet m g = Ideal.Quotient.mk _ Q ↔
      ∀ e : κ →₀ ℕ, Finsupp.degree e < m + 1 → coeff e g = Q.coeff e := by
  unfold toJet
  rw [jet_mk_eq_iff]
  refine forall₂_congr fun e he => ?_
  rw [coeff_truncTotal_eq_ite, if_pos he]

theorem toJet_eq_iff (m : ℕ) (g g' : MvPowerSeries κ R) :
    toJet m g = toJet m g' ↔ ∀ e : κ →₀ ℕ, Finsupp.degree e < m + 1 → coeff e g = coeff e g' := by
  refine (toJet_eq_mk_iff m g _).trans (forall₂_congr fun e he => ?_)
  rw [coeff_truncTotal_eq_ite, if_pos he]

theorem toJet_coe (m : ℕ) (Q : MvPolynomial κ R) :
    toJet m (Q : MvPowerSeries κ R) = Ideal.Quotient.mk _ Q :=
  (toJet_eq_mk_iff m _ Q).2 fun e _ => MvPolynomial.coeff_coe Q e


variable (R κ) in
def toJetHom (m : ℕ) : MvPowerSeries κ R →ₐ[R] JetR R κ m :=
  (truncTotalAlgHom κ R (m + 1)).restrictScalars R

theorem toJetHom_apply (m : ℕ) (g : MvPowerSeries κ R) : toJetHom R κ m g = toJet m g := rfl

theorem jetTruncR_toJet (m : ℕ) (g : MvPowerSeries κ R) :
    jetTruncR R κ m (toJet (m + 1) g) = toJet m g := by
  symm
  refine (toJet_eq_mk_iff m g (truncTotal (m + 1 + 1) g)).2 fun e he => ?_
  rw [coeff_truncTotal_eq_ite, if_pos (by omega)]

theorem jetAug_toJet (m : ℕ) (g : MvPowerSeries κ R) :
    jetAug R κ m (toJet m g) = constantCoeff g := by
  show MvPolynomial.aeval (fun _ : κ => (0 : R)) (truncTotal (m + 1) g) = _
  rw [MvPolynomial.aeval_zero', MvPolynomial.constantCoeff_eq, coeff_truncTotal_eq_ite, if_pos (by simp)]
  rfl

theorem eq_of_toJet_eq {g g' : MvPowerSeries κ R} (h : ∀ m, toJet m g = toJet m g') : g = g' := by
  ext e
  exact (toJet_eq_iff _ g g').1 (h (Finsupp.degree e)) e (Nat.lt_succ_self _)

theorem exists_toJet_eq (p : ∀ m, JetR R κ m) (hp : ∀ m, jetTruncR R κ m (p (m + 1)) = p m) :
    ∃ g : MvPowerSeries κ R, ∀ m, toJet m g = p m := by
  choose P hP using fun m => Ideal.Quotient.mk_surjective (p m)
  have h1 : ∀ m (e : κ →₀ ℕ), Finsupp.degree e < m + 1 → (P (m + 1)).coeff e = (P m).coeff e := fun m => by
    rw [← jet_mk_eq_iff, hP m, ← hp m, ← hP (m + 1)]
    rfl
  have h2 : ∀ (e : κ →₀ ℕ) m, Finsupp.degree e ≤ m → (P (Finsupp.degree e)).coeff e = (P m).coeff e := by
    intro e m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [ih, h1 m e (by omega)]
  refine ⟨fun e => (P (Finsupp.degree e)).coeff e, fun m => ?_⟩
  rw [← hP m]
  exact (toJet_eq_mk_iff m _ _).2 fun e he => h2 e m (by omega)

theorem exists_jetHom {σ : Type} (a : σ → MvPowerSeries κ R) (ha : ∀ j, constantCoeff (a j) = 0) (m : ℕ) :
    ∃ ψ : JetR R σ m →ₐ[R] JetR R κ m, ∀ j, ψ (zR m j) = toJet m (a j) :=
  ⟨jetLift R (RingHom.ker (jetAug R κ m)) (ker_jetAug_pow κ m) (fun j => toJet m (a j))
    (fun j => (jetAug_toJet m (a j)).trans (ha j)), fun j => jetLift_zR _ _ _ _ j⟩

theorem jetHom_toJet {σ : Type} [Finite σ] (a : σ → MvPowerSeries κ R) (ha : ∀ j, constantCoeff (a j) = 0) (m : ℕ)
    (ψ : JetR R σ m →ₐ[R] JetR R κ m) (hψ : ∀ j, ψ (zR m j) = toJet m (a j)) (g : MvPowerSeries σ R) :
    ψ (toJet m g) = toJet m (subst a g) := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hpoly : ∀ Q : MvPolynomial σ R, ψ (Ideal.Quotient.mk _ Q) = toJet m (subst a (Q : MvPowerSeries σ R)) := by
    intro Q
    rw [subst_coe, ← toJetHom_apply]
    have : ψ.comp (Ideal.Quotient.mkₐ R _) = (toJetHom R κ m).comp (MvPolynomial.aeval a) := by
      apply MvPolynomial.algHom_ext
      intro j
      rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.aeval_X, toJetHom_apply]
      exact hψ j
    exact AlgHom.congr_fun this Q
  refine (hpoly (truncTotal (m + 1) g)).trans ((toJet_eq_iff m _ _).2 fun e he => ?_)
  set r : MvPowerSeries σ R := (truncTotal (m + 1) g : MvPolynomial σ R) - g with hr
  have hro : ((m + 1 : ℕ) : ℕ∞) ≤ r.order := nat_le_order fun d hd => by
    rw [hr, map_sub, MvPolynomial.coeff_coe, coeff_truncTotal_eq_ite, if_pos hd, sub_self]
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (a i).order := le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.2 (ha i)
  have h2 : ((m + 1 : ℕ) : ℕ∞) ≤ (subst a r).order := by
    refine le_trans ?_ (le_order_subst hs r)
    calc ((m + 1 : ℕ) : ℕ∞) = 1 * ((m + 1 : ℕ) : ℕ∞) := (one_mul _).symm
      _ ≤ _ := mul_le_mul' h1 hro
  have h3 : coeff e (subst a r) = 0 := coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast he) h2)
  rwa [hr, ← substAlgHom_apply hs, map_sub, map_sub, sub_eq_zero, substAlgHom_apply, substAlgHom_apply] at h3

theorem jetAlg : JetAlgSt := fun R _ κ _ =>
  ⟨fun m => ⟨toJetHom R κ m, fun _ => rfl, fun j => toJet_X m j⟩,
    fun m g => ⟨jetTruncR_toJet m g, jetAug_toJet m g⟩,
    fun _ _ h => eq_of_toJet_eq h, exists_toJet_eq,
    fun _ _ a ha m => ⟨exists_jetHom a ha m, jetHom_toJet a ha m⟩⟩

end GlobalTheory.JetSer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsUniqueNormPrim
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (LBIso)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetSer

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_gen_of_lbIso {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (X ⟶ X)) (ε : K → ℤ)
    (H : LBIso L (LB.LinComb L φ ε)) :
    ∃ t : LB.Gen (LB.LinComb L (K := K ⊕ PUnit) (Sum.elim φ (fun _ => 𝟙 X)) (Sum.elim ε (fun _ => -1))), t.IsGen := by
  obtain ⟨v, hv⟩ := H
  have le : ∀ j : K ⊕ PUnit → L.ι, LB.wchart L (Sum.elim φ (fun _ : PUnit => 𝟙 X)) j ≤
      LB.wchart L φ (j ∘ Sum.inl) ⊓ L.U (j (Sum.inr PUnit.unit)) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k), Set.mem_iInter.1 hy (Sum.inr PUnit.unit)⟩
  refine ⟨⟨fun j => res (le j) (v.s (j ∘ Sum.inl, j (Sum.inr PUnit.unit)))⟩,
    fun (p q : K ⊕ PUnit → L.ι) => unit_ext fun y hy => ?_⟩
  have hm : (𝟙 X : X ⟶ X) y ∈ LB.wchart L φ (p ∘ Sum.inl) ⊓ L.U (p (Sum.inr PUnit.unit)) ⊓
      (LB.wchart L φ (q ∘ Sum.inl) ⊓ L.U (q (Sum.inr PUnit.unit))) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 X) y (LB.wchart L φ (p ∘ Sum.inl) ⊓ L.U (p (Sum.inr PUnit.unit)) ⊓
      (LB.wchart L φ (q ∘ Sum.inl) ⊓ L.U (q (Sum.inr PUnit.unit)))))
    (hv (p ∘ Sum.inl, p (Sum.inr PUnit.unit)) (q ∘ Sum.inl, q (Sum.inr PUnit.unit)))
  have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_div L (LB.LinComb L φ ε) (𝟙 X) y (p ∘ Sum.inl, p (Sum.inr PUnit.unit))
      (q ∘ Sum.inl, q (Sum.inr PUnit.unit)) hm).trans (congrArg₂ (· * ·)
        (gm_linComb L φ ε (𝟙 X) y _ _ hm.1.1 hm.2.1) rfl)) (gm_res _ y _ hm _))))
  refine ((gm_res (𝟙 X) y _ hy _).trans (gm_res (𝟙 X) y (le p) hy.1 _)).trans (e'.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L _ _ (𝟙 X) y p q hy.1 hy.2).trans ?_)
    ((gm_res (𝟙 X) y _ hy _).trans (gm_res (𝟙 X) y (le q) hy.2 _)))
  exact DVR.prod_sum₂ (K := K) (K' := PUnit) _ rfl ((Fintype.prod_unique _).trans (zpow_neg_one _))

theorem gen_ext_val {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t t' : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (ht' : t'.IsGen)
    (h : ∀ y J, Good L y J → val t (𝟙 Y) y J = val t' (𝟙 Y) y J) : t.s = t'.s := by
  funext j
  exact Units.ext (sec_ext_val hL (s := genSec t ht) (s' := genSec t' ht') (fun y J hJ => by
    rw [sval_genSec t ht _ y hJ, sval_genSec t' ht' _ y hJ, h y J hJ]) j)

theorem prod_lam {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] (x y : T ⟶ G) {U : Type} [CommGroup U]
    (h : (T.left ⟶ G.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (psum G ![x, y] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ G).left := by
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => h (psum G ![x, y] I).left ^ ((-1 : ℤ) ^ (2 - I.card))) (fun I => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₄ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  rw [p₀, p₁, p₂, p₄]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₄ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₄]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem prod_prim {S : Scheme.{0}} {G T : Over S} [GrpObj G] (w : G ⟶ G) (x : T ⟶ G) {U : Type} [CommGroup U]
    (h : (T.left ⟶ G.left) → U) :
    ∏ i, h (x.left ≫ primφ w i) ^ primε i =
      h x.left * (h (x * (x ≫ w)).left)⁻¹ * h x.left * h (x ≫ w).left * (h (1 : T ⟶ G).left)⁻¹ := by
  have e₁ : x ≫ (𝟙 G * w) = x * (x ≫ w) := (MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id])
  have e₄ : x ≫ (1 : G ⟶ G) = 1 := MonObj.comp_one _
  rw [Fin.prod_univ_five]
  show h (x.left ≫ 𝟙 _) ^ (1 : ℤ) * h (x ≫ (𝟙 G * w)).left ^ (-1 : ℤ) * h (x.left ≫ 𝟙 _) ^ (1 : ℤ) *
    h (x ≫ w).left ^ (1 : ℤ) * h (x ≫ (1 : G ⟶ G)).left ^ (-1 : ℤ) = _
  rw [e₁, e₄, Category.comp_id]
  simp only [zpow_neg, zpow_one]

theorem exists_unique_normPrim : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (Lr : RigLB G) (w : G ⟶ G) [IsMonHom w],
    LBIso Lr.L (cubeLB G ![𝟙 G, w] Lr.L) →
    (∃ ρ : LB.Gen (LB.LinComb Lr.L (primφ w) primε), ρ.IsGen ∧
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ ρ (eSec G)) Lr.rig) ∧
    (Function.Surjective G.hom.appTop.hom → ∀ ρ ρ' : LB.Gen (LB.LinComb Lr.L (primφ w) primε), ρ.IsGen → ρ'.IsGen →
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ ρ (eSec G)) Lr.rig →
      LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ ρ' (eSec G)) Lr.rig → ρ.s = ρ'.s) := by
  intro S G _ _ Lr w _ H
  have he : eSec G ≫ G.hom = 𝟙 S := Over.w η[G]
  refine ⟨?_, fun hp ρ ρ' h h' c c' => gen_ext_val Lr.isLB h h' fun y J hJ =>
    gen_unique Lr.isLB G.hom (eSec G) he hp h h' (fun y J hJ => ?_) _ _ y J hJ⟩
  · obtain ⟨t₀, ht₀⟩ := exists_gen_of_lbIso Lr.L _ _ H
    have P : ∀ (V : Type) [CommGroup V] (k : (G.left ⟶ G.left) → V), ∏ i, k (primφ w i) ^ primε i =
        k (𝟙 _) * (k (𝟙 G * w : G ⟶ G).left)⁻¹ * k (𝟙 _) * k w.left * (k (1 : G ⟶ G).left)⁻¹ := fun V _ k => by
      have := prod_prim w (𝟙 G) k
      simpa only [Over.id_left, Category.id_comp] using this
    obtain ⟨t, ht, -⟩ := exists_gen Lr.isLB (φ' := primφ w) (ε' := primε) (fun V _ k => by
      refine (DVR.prod_neg _ _ (DVR.prod_sum₂ (K' := PUnit) (U := V) _ (prod_lam (𝟙 G) w k)
        (c' := (k (𝟙 _))⁻¹) (by simp))).trans ?_
      rw [P]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, Over.id_left]
      abel) _ (DVR.invGen_isGen _ _ _ _ ht₀)
    have n : G.hom ≫ eSec G = (1 : G ⟶ G).left := rfl
    obtain ⟨ρ, hρ, hv⟩ := exists_gen Lr.isLB (φ' := primφ w) (ε' := primε) (fun V _ k => by
      have p := prod_prim w (1 : G ⟶ G) k
      rw [MonObj.one_comp, _root_.mul_one] at p
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 5) (K' := Fin 5 ⊕ PUnit) (U := V) _
        (c := ∏ i, k (primφ w i) ^ primε i) rfl
        (DVR.prod_sum₂ (K := Fin 5) (K' := PUnit) (U := V) _ (DVR.prod_neg _ _ p) (c' := k (1 : G ⟶ G).left)
          (by rw [Fintype.prod_unique]; exact zpow_one _))) ?_
      simp)
      (LB.mulGen Lr.L _ _ _ _ t (LB.mulGen Lr.L _ _ _ _
        (LB.invGen Lr.L _ _ (LB.pullGen Lr.L _ _ t (1 : G ⟶ G).left)) (LB.pullGen Lr.L _ _ Lr.rig G.hom)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)) (DVR.pullGen_isGen _ _ _ _ Lr.rigGen _)))
    refine ⟨ρ, hρ, corr_of_val Lr.isLB fun y J hJ => ?_⟩
    have e₁ : eSec G ≫ (1 : G ⟶ G).left = eSec G := by
      rw [← n, ← Category.assoc, he]; exact Category.id_comp _
    rw [val_pull hJ, Category.id_comp, hv _ _ y J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, e₁,
      mul_inv_cancel_left]
    exact congrArg (fun q => val Lr.rig q y J) he
  · have a := val_corr hJ c (𝟙 _)
    have b := val_corr hJ c' (𝟙 _)
    rw [val_pull hJ, Category.id_comp] at a b
    exact a.trans b.symm

end GlobalTheory.JetSer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsUniversalThickening
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.IsolPt

theorem isArtinianRing_of_finite_points (k B : Type) [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] [Finite (B →ₐ[k] AlgebraicClosure k)] : IsArtinianRing B := by
  have hN : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hJ : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k)
  have hsur : ∀ m : Ideal B, m.IsMaximal → ∃ f : B →ₐ[k] AlgebraicClosure k, RingHom.ker f = m := by
    intro m hm
    letI := Ideal.Quotient.field m
    have : Module.Finite k (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ m)
    let g : (B ⧸ m) →ₐ[k] AlgebraicClosure k := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨g.comp (Ideal.Quotient.mkₐ k m), ?_⟩
    ext b
    simp only [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [map_eq_zero_iff g g.toRingHom.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hfin : {m : Ideal B | m.IsMaximal}.Finite :=
    (Set.finite_range fun f : B →ₐ[k] AlgebraicClosure k => RingHom.ker f).subset hsur
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
  intro p hp
  have h1 : p.jacobson = p := IsJacobsonRing.out hJ hp.isRadical
  have hf : {J : Ideal B | p ≤ J ∧ J.IsMaximal}.Finite := hfin.subset fun _ h => h.2
  have h2 : hf.toFinset.inf id ≤ p := by
    rw [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset]
    exact h1.le
  obtain ⟨m, hm, hle⟩ := hp.inf_le'.1 h2
  rw [Set.Finite.mem_toFinset] at hm
  have : m = p := le_antisymm hle hm.1
  exact this ▸ hm.2

theorem exists_pow_stable {B : Type} [CommRing B] [IsArtinianRing B] (I : Ideal B) :
    ∃ M : ℕ, ∀ j : ℕ, I ^ (M + 1) ≤ I ^ (j + 1) := by
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := B) (M := B)
    ⟨fun n => OrderDual.toDual (I ^ n), fun _ _ h => Ideal.pow_le_pow_right h⟩
  refine ⟨n, fun j => ?_⟩
  have h1 : I ^ n = I ^ (n + (j + 1)) := hn (n + (j + 1)) (by omega)
  calc I ^ (n + 1) ≤ I ^ n := Ideal.pow_le_pow_right (by omega)
    _ = I ^ (n + (j + 1)) := h1
    _ ≤ I ^ (j + 1) := Ideal.pow_le_pow_right (by omega)

theorem exists_thickening {k B : Type} [Field k] [CommRing B] [Algebra k B] [IsArtinianRing B]
    (e : B →ₐ[k] k) : ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (aug : A →ₐ[k] k) (M : ℕ)
      (π : B →ₐ[k] A), RingHom.ker aug ^ (M + 1) = ⊥ ∧ aug.comp π = e ∧
      ∀ (Q : Type) [CommRing Q] [Algebra k Q] (augQ : Q →ₐ[k] k) (j : ℕ),
        RingHom.ker augQ ^ (j + 1) = ⊥ → ∀ z : B →ₐ[k] Q, augQ.comp z = e →
        ∃ a : A →ₐ[k] Q, augQ.comp a = aug ∧ z = a.comp π := by
  obtain ⟨M, hM⟩ := exists_pow_stable (RingHom.ker e)
  set I : Ideal B := RingHom.ker e ^ (M + 1) with hI
  have hIe : ∀ b ∈ I, e b = 0 := fun b hb => Ideal.pow_le_self (Nat.succ_ne_zero M) hb
  refine ⟨B ⧸ I, inferInstance, inferInstance, Ideal.Quotient.liftₐ I e hIe, M, Ideal.Quotient.mkₐ k I,
    ?_, ?_, ?_⟩
  · have h : RingHom.ker (Ideal.Quotient.liftₐ I e hIe) ≤ (RingHom.ker e).map (Ideal.Quotient.mk I) := by
      intro x hx
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact Ideal.mem_map_of_mem _ hx
    refine le_bot_iff.1 ((Ideal.pow_right_mono h _).trans ?_)
    rw [← Ideal.map_pow, ← hI, Ideal.map_quotient_self]
  · ext b
    rfl
  · intro Q _ _ augQ j hj z hz
    have hzI : ∀ b ∈ I, z b = 0 := by
      intro b hb
      have h : (RingHom.ker e).map z ≤ RingHom.ker augQ := by
        rw [Ideal.map_le_iff_le_comap]
        intro c hc
        change augQ (z c) = 0
        rw [← AlgHom.comp_apply, hz]
        exact hc
      have h2 := Ideal.mem_map_of_mem z (hM j hb)
      rw [Ideal.map_pow] at h2
      have h3 := Ideal.pow_right_mono h _ h2
      rwa [hj] at h3
    refine ⟨Ideal.Quotient.liftₐ I z hzI, ?_, ?_⟩
    · apply Ideal.Quotient.algHom_ext
      ext b
      exact DFunLike.congr_fun hz b
    · ext b
      rfl

theorem exists_factor {k A B : Type} [CommRing k] [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    {X : Over (Spec (CommRingCat.of k))} (x : Chart.sp (R₀ := k) A ⟶ X) (v : Chart.sp (R₀ := k) B ⟶ X)
    [IsOpenImmersion v.left] (hsub : Set.range x.left ⊆ Set.range v.left) :
    ∃ ψ : B →ₐ[k] A, x = Chart.spMap ψ ≫ v := by
  have hl := IsOpenImmersion.lift_fac v.left _ hsub
  obtain ⟨ψ, hψ⟩ := NatFun.spMap_surjective (k := k) (A := B) (B := A)
    (Over.homMk (IsOpenImmersion.lift v.left _ hsub) (by
      rw [← Over.w v, ← Category.assoc, hl, Over.w]))
  refine ⟨ψ, Over.OverMorphism.ext ?_⟩
  rw [hψ]
  exact hl.symm

theorem surjective_spMap_aug {k Q : Type} [Field k] [CommRing Q] [Algebra k Q] (q : Q →ₐ[k] k) (j : ℕ)
    (hj : RingHom.ker q ^ (j + 1) = ⊥) : Function.Surjective (Chart.spMap q).left := by
  intro p
  have hq : Function.Surjective q.toRingHom := fun c => ⟨algebraMap k Q c, q.commutes c⟩
  let p' : PrimeSpectrum Q := p
  haveI := p'.isPrime
  have hker : RingHom.ker q.toRingHom ≤ p'.asIdeal :=
    p'.isPrime.le_of_pow_le (n := j + 1) (le_of_eq_of_le hj bot_le)
  have hprime : (p'.asIdeal.map q.toRingHom).IsPrime := Ideal.map_isPrime_of_surjective hq hker
  refine ⟨(⟨p'.asIdeal.map q.toRingHom, hprime⟩ : PrimeSpectrum k), ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap q.toRingHom (Ideal.map q.toRingHom p'.asIdeal) = p'.asIdeal
  rw [Ideal.comap_map_of_surjective' q.toRingHom hq, sup_eq_left.mpr hker]


open NatFun in
theorem exists_universal_thickening : ∀ (k : Type) [Field k] (K : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType K.hom], (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Spec (CommRingCat.of k)), Finite (Over.mk t ⟶ K)) → ∀ e : Chart.sp (R₀ := k) k ⟶ K, ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (aug : A →ₐ[k] k) (M : ℕ) (io : Chart.sp (R₀ := k) A ⟶ K), RingHom.ker aug ^ (M + 1) = ⊥ ∧ Chart.spMap aug ≫ io = e ∧ ∀ (Q : Type) [CommRing Q] [Algebra k Q] (augQ : Q →ₐ[k] k) (j : ℕ), RingHom.ker augQ ^ (j + 1) = ⊥ → ∀ z : Chart.sp (R₀ := k) Q ⟶ K, Chart.spMap augQ ≫ z = e → ∃ a : A →ₐ[k] Q, augQ.comp a = aug ∧ z = Chart.spMap a ≫ io := by
  intro k _ K _ hfin e
  let o : (Chart.sp (R₀ := k) k).left := (⊥ : PrimeSpectrum k)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := K.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (e.left o)) isOpen_univ
  change IsAffineOpen U at hU
  let v : Chart.sp (R₀ := k) Γ(K.left, U) ⟶ K := affinePoint hU
  haveI : IsOpenImmersion v.left := hU.isOpenImmersion_fromSpec
  haveI : Mono v := Over.mono_of_mono_left v
  have hinj : ∀ (Q : Type) [CommRing Q] [Algebra k Q],
      Function.Injective fun f : Γ(K.left, U) →ₐ[k] Q => Chart.spMap f ≫ v := by
    intro Q _ _ f g h
    exact spMap_injective ((cancel_mono v).1 h)
  have hft : Algebra.FiniteType k Γ(K.left, U) := by
    have h : LocallyOfFiniteType (v.left ≫ K.hom) := inferInstance
    rw [Over.w v] at h
    have h2 := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h
    exact RingHom.finiteType_algebraMap.1 h2
  haveI : Finite (Chart.sp (R₀ := k) (AlgebraicClosure k) ⟶ K) := hfin _ _
  haveI : Finite (Γ(K.left, U) →ₐ[k] AlgebraicClosure k) := Finite.of_injective _ (hinj _)
  haveI := isArtinianRing_of_finite_points k Γ(K.left, U)
  have he : Set.range e.left ⊆ Set.range v.left := by
    rintro _ ⟨y, rfl⟩
    have : y = o := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [this]
    exact hU.range_fromSpec.superset hxU
  obtain ⟨e₀, he₀⟩ := exists_factor e v he
  obtain ⟨A, _, _, aug, M, π, h1, h2, h3⟩ := exists_thickening e₀
  refine ⟨A, _, _, aug, M, Chart.spMap π ≫ v, h1, ?_, ?_⟩
  · rw [← Category.assoc, Chart.spMap_comp, h2, he₀]
  · intro Q _ _ augQ j hj z hz
    have hzr : Set.range z.left ⊆ Set.range v.left := by
      rintro _ ⟨y, rfl⟩
      obtain ⟨y', rfl⟩ := surjective_spMap_aug augQ j hj y
      apply he
      exact ⟨y', by rw [← hz]; rfl⟩
    obtain ⟨z₀, rfl⟩ := exists_factor z v hzr
    rw [← Category.assoc, Chart.spMap_comp, he₀] at hz
    obtain ⟨a, ha, rfl⟩ := h3 Q augQ j hj z₀ (hinj _ hz)
    exact ⟨a, ha, by rw [← Category.assoc, Chart.spMap_comp]⟩

end GlobalTheory.IsolPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MulFConstAndMap
section
noncomputable section
open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.FormalMul

theorem constantCoeff_mulF {T : Type} [CommRing T] {d : ℕ} (F : Fin d → PS T 2 d)
    (hF : ∀ i, constantCoeff (F i) = 0) (N : ℕ) : ∀ j, constantCoeff (mulF F N j) = 0 := by
  induction N with
  | zero => intro j; simp [mulF]
  | succ n ih => exact gp_addOf F hF _ _ ih (gp_pt 0)

theorem mulF_map {T O : Type} [CommRing T] [CommRing O] (io : T →+* O) {d : ℕ} (F : Fin d → PS T 2 d)
    (hF : ∀ i, constantCoeff (F i) = 0) (N : ℕ) :
    ∀ j, mulF (fun i => MvPowerSeries.map io (F i)) N j = MvPowerSeries.map io (mulF F N j) := by
  induction N with
  | zero => intro j; simp [mulF]
  | succ n ih =>
    intro j
    have hs := gt_hasSubst ![mulF F n, pt T (n := 1) d 0]
      (pair_points_zero_constant (constantCoeff_mulF F hF n) (gp_pt 0))
    simp only [mulF, addOf, ev]
    rw [MvPowerSeries.map_subst hs]
    congr 1
    funext p
    rcases p with ⟨a, b⟩
    fin_cases a
    · exact ih b
    · simp [pt]

theorem mulF_const_and_map : ∀ (T O : Type) [CommRing T] [CommRing O] (io : T →+* O) (d : ℕ) (F : FGLaw T d)
    (N : ℕ) (j : Fin d), MvPowerSeries.constantCoeff (mulF F.F N j) = 0 ∧
      mulF (F.mapF io) N j = MvPowerSeries.map io (mulF F.F N j) :=
  fun _ _ _ _ io _ F N j => ⟨constantCoeff_mulF F.F F.const N j, mulF_map io F.F F.const N j⟩

end GlobalTheory.FormalMul
end
end

