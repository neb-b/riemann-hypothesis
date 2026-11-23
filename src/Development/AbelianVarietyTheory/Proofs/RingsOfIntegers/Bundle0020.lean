module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ChangeChart

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SpanEqTopOfCard
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace BoxSpan

theorem span_eq_top_of_card {C M : Type} [CommRing C] (hC : IsField C) [AddCommGroup M] [Module C M]
    {I I' : Type} [Fintype I] [Fintype I'] (b : I → M) (hli : LinearIndependent C b)
    (hsp : Submodule.span C (Set.range b) = ⊤) (v : I' → M) (hv : LinearIndependent C v)
    (hc : Fintype.card I' = Fintype.card I) : Submodule.span C (Set.range v) = ⊤ := by
  let _ : Field C := hC.toField
  have hb : Module.finrank C M = Fintype.card I :=
    Module.finrank_eq_card_basis (Module.Basis.mk hli hsp.ge)
  have _ : Module.Finite C M := Module.Finite.of_basis (Module.Basis.mk hli hsp.ge)
  exact hv.span_eq_top_of_card_eq_finrank' (hc.trans hb.symm)

theorem exists_basis (hS : SecBaseChangeSt) {K : Type} [Field K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ)
    (hn : 1 ≤ n) (F : Type) [CommRing F] (q : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K)) :
    ∃ b : Fin (n ^ P.g) → SecM P.A P.L n (Over.mk q), LinearIndependent Γ((Over.mk q).left, ⊤) b ∧
      Submodule.span Γ((Over.mk q).left, ⊤) (Set.range b) = ⊤ := by
  obtain ⟨V, hpV, b, hb⟩ := hS (Spec (CommRingCat.of K)) P n hn default
  have hbo : (baseOver (Spec (CommRingCat.of K))).hom = 𝟙 _ := rfl
  have hr : Set.range q ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : q x = default := Subsingleton.elim _ _
    rw [this]
    exact hpV
  obtain ⟨t, rfl⟩ : ∃ t : Spec (CommRingCat.of F) ⟶ V.toScheme, t ≫ V.ι ≫ (baseOver (Spec (CommRingCat.of K))).hom = q := by
    refine ⟨IsOpenImmersion.lift V.ι q hr, ?_⟩
    rw [hbo]
    erw [Category.comp_id]
    exact IsOpenImmersion.lift_fac _ _ _
  unfold LPow at b
  choose b' hb' using fun i => GlobalTheory.IndivisibleSection.exists_pull_chart (b i) (homAt (V := V) t ▷ P.A).left
    (fun _ => (snd (baseAt (V := V) t) P.A).left) (fun _ => by rw [← Over.comp_left, whiskerRight_snd])
  obtain ⟨hli, hsp⟩ := hb F t b' (fun i j => hb' i j _)
  exact ⟨fun i => SecM.ofSec P.A (b' i), hli, hsp⟩

theorem comb_apply {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) (T : Over S) {I : Type}
    [Fintype I] (c : I → Γ(T.left, ⊤)) (v : I → SecM A L a T) (jj) :
    (∑ l, c l • v l).1 jj = ∑ l, liftFun A _ (c l) * (v l).1 jj := by
  rw [Submodule.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun l _ => rfl

private theorem ΓSpecIso_inv_hom_apply (F : Type) [CommRing F] (x : Γ(Spec (CommRingCat.of F), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom x) = x := by
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

end BoxSpan


open BoxSpan in
theorem boxProduct_span : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ s : LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ))), ∃ (n : ℕ) (c : Fin n → F) (t : Fin n → Fin j → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))) (t' : Fin n → LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ)))), (∀ l, (∀ (Z : Scheme.{0}) (r : Z ⟶ ((TFK (R := R) F) ⊗ A'.A).left) (z : Z) (J J'), Geo.Tor.Good A.L z J → Geo.Tor.Good A'.L z J' → (bw pA.w (r ≫ (snd (TFK (R := R) F) A'.A).left) z (fun i => J ((r ≫ (snd (TFK (R := R) F) A'.A).left) ≫ (pA.pr i).left)) (J' (r ≫ (snd (TFK (R := R) F) A'.A).left)) ^ k).val * Geo.Tor.sval (t' l) r z J' = ∏ i, Geo.Tor.sval (t l i) (r ≫ ((TFK (R := R) F) ◁ pA.pr i).left) z J)) ∧ ∀ jj, s.f jj = ∑ l, liftFun A'.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) * (t' l).f jj := by
  intro hL R _ _ j A A' pA F _ _ k hk s
  obtain ⟨b, hbi, -⟩ := exists_basis hL.secBaseChange A k hk F (TFK (R := R) F).hom
  obtain ⟨b', hbi', hbs'⟩ := exists_basis hL.secBaseChange A' k hk F (TFK (R := R) F).hom
  let σ : Fin (k ^ A.g) → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left)
      (fun _ => (k : ℤ))) := fun l => ⟨(b l).1, fun i i' => (b l).2 i i'⟩
  have hb : ∀ c : Fin (k ^ A.g) → F, (∀ jj, ∑ l, liftFun A.A _
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) * (σ l).f jj = 0) → c = 0 := by
    intro c hc
    have h0 := Fintype.linearIndependent_iff.mp hbi
      (fun l => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c l)) (by
        apply Subtype.ext
        funext jj
        exact (comb_apply A.A A.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) _ b jj).trans (hc jj))
    funext l
    have h1 := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (h0 l)
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero] at h1
    exact h1
  choose t' ht' using fun a : Fin j → Fin (k ^ A.g) =>
    exists_boxSec_pow_ext R j A A' pA F k (fun i => σ (a i))
  have hind := boxProduct_linearIndependent R j A A' pA F k (k ^ A.g) σ hb t' ht'
  have hli : LinearIndependent Γ((Over.mk (TFK (R := R) F).hom).left, ⊤)
      (fun a => (SecM.ofSec A'.A (t' a) : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg a
    have hc := hind (fun a => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (g a)) (by
      intro jj
      have h1 := congrArg (fun x : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) => x.1 jj) hg
      have h2 := (comb_apply A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) g
        (fun a => SecM.ofSec A'.A (t' a)) jj).symm.trans h1
      refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) h2
      exact congrArg (fun x => liftFun (T := TFK (R := R) F) A'.A _ x * (t' a).f jj) (ΓSpecIso_inv_hom_apply F (g a)))
    have h2 := congrFun hc a
    rw [Pi.zero_apply] at h2
    rw [← ΓSpecIso_inv_hom_apply F (g a), h2, map_zero]
  have hfield : IsField Γ((Over.mk (TFK (R := R) F).hom).left, ⊤) :=
    MulEquiv.isField (Field.toIsField F)
      (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toMulEquiv
  have hcard : Fintype.card (Fin j → Fin (k ^ A.g)) = Fintype.card (Fin (k ^ A'.g)) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, polAV_g_of_isPowPolAV _ j A A' pA, ← pow_mul,
      mul_comm]
    exact (Fintype.card_fin _).symm
  have hspan := span_eq_top_of_card hfield b' hbi' hbs' _ hli hcard
  have hmem : (SecM.ofSec A'.A s : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom)) ∈
      Submodule.span Γ((Over.mk (TFK (R := R) F).hom).left, ⊤)
        (Set.range fun a => (SecM.ofSec A'.A (t' a) : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom))) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨g, hg⟩ := Submodule.mem_span_range_iff_exists_fun _ |>.mp hmem
  let e := Fintype.equivFin (Fin j → Fin (k ^ A.g))
  refine ⟨Fintype.card (Fin j → Fin (k ^ A.g)), fun l => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (g (e.symm l)),
    fun l i => σ (e.symm l i), fun l => t' (e.symm l), fun l => ht' (e.symm l), ?_⟩
  intro jj
  have h1 := congrArg (fun x : SecM A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) => x.1 jj) hg
  have h2 := (comb_apply A'.A A'.L (k : ℤ) (Over.mk (TFK (R := R) F).hom) g
    (fun a => SecM.ofSec A'.A (t' a)) jj).symm.trans h1
  refine h2.symm.trans ?_
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  congr 1
  exact (ΓSpecIso_inv_hom_apply F _).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SquareRes
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowUnif

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig

variable {B B' G G' T T' S₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {j : ℕ}
  {pr : Fin j → (B' ⟶ B)} {prG : Fin j → (G' ⟶ G)} {p : T ⟶ B} {p' : T' ⟶ B'} {f : T ⟶ G} {f' : T' ⟶ G'}

private theorem sec_res_comp_algebraMap {X : Scheme.{0}} {U V W : X.Opens} (h₁ : U ≤ V) (h₂ : V ≤ W)
    (x : Γ(X, W)ˣ) : res h₁ (res h₂ x) = res (h₁.trans h₂) x := by
  apply Units.ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private theorem res_self_lemma {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (x : Γ(X, U)ˣ) : res h x = x := by
  apply Units.ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  have e : homOfLE h = 𝟙 U := rfl
  rw [e, op_id, CategoryTheory.Functor.map_id]
  rfl

private theorem linComb_comp_U_le_linComb_linComb_U {eG' : S₀ ⟶ G'} (jN : Fin j → L.ι) :
    (LB.LinComb L (fun i => eG' ≫ prG i) (fun _ => 1)).U jN ≤
      (LB.LinComb (LB.LinComb L prG (fun _ => 1)) (K := PUnit) (fun _ => eG') (fun _ => 1)).U (fun _ => jN) := by
  intro x hx
  simp only [LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage,
    SetLike.mem_coe] at hx ⊢
  intro _ k
  simpa using hx k

private theorem linComb_unit_U_le {X Y : Scheme.{0}} (N : LB X) (e : Y ⟶ X) (a b : N.ι) :
    (LB.LinComb N (K := PUnit) (fun _ => e) (fun _ => 1)).U (fun _ => a) ⊓
      (LB.LinComb N (K := PUnit) (fun _ => e) (fun _ => 1)).U (fun _ => b) ≤ e ⁻¹ᵁ (N.U a ⊓ N.U b) := by
  intro x hx
  simp only [LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage,
    SetLike.mem_coe, Scheme.Hom.mem_preimage, TopologicalSpace.Opens.mem_inf] at hx ⊢
  exact ⟨hx.1 PUnit.unit, hx.2 PUnit.unit⟩

private theorem linComb_unit_g_eq {X Y : Scheme.{0}} (N : LB X) (e : Y ⟶ X) (a b : N.ι) :
    (LB.LinComb N (K := PUnit) (fun _ => e) (fun _ => 1)).g (fun _ => a) (fun _ => b) =
      res (linComb_unit_U_le N e a b) (pullU e (N.U a ⊓ N.U b) (N.g a b)) := by
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one, pow_one]
  rfl

private theorem res_pullU_id_eq_res'' {X : Scheme.{0}} {U V : X.Opens} (x : Γ(X, U)ˣ) (h : V ≤ (𝟙 X) ⁻¹ᵁ U) :
    res h (pullU (𝟙 X) U x) = res (fun y hy => h hy) x := by
  apply Units.ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rfl

private theorem res_congr_of_index_eq {X : Scheme.{0}} {Idx : Type*} {U : Idx → X.Opens} (s : ∀ a, Γ(X, U a)ˣ) {V : X.Opens}
    {a b : Idx} (e : a = b) (h₁ : V ≤ U a) (h₂ : V ≤ U b) : res h₁ (s a) = res h₂ (s b) := by
  subst e
  rfl

theorem idIso_rig (hL : L.IsLB) {eG : S₀ ⟶ G} {eG' : S₀ ⟶ G'} (rL : LB.Gen (L.pull eG))
    (hG : ∀ (i : Fin j) (_ : PUnit), eG' ≫ prG i = 𝟙 S₀ ≫ eG)
    (hr : (GeneratorPullback.boxGen L prG (fun _ : PUnit => eG') (fun _ => 1)
      (fun i => GeneratorPullback.pullAlong L (prG i) (𝟙 S₀) (fun _ => eG) (fun _ => 1) (fun _ => eG') (hG i) rL)).IsGen) :
    ∃ b : LB.Gen (LB.LinComb L (K := Fin j) (fun i => eG' ≫ prG i) (fun _ => 1)),
      GeneratorPullback.MapsAt L (LB.LinComb L prG (fun _ => 1)) prG (idIso _) eG' 1
        (GeneratorPullback.boxGen L prG (fun _ : PUnit => eG') (fun _ => 1)
          (fun i => GeneratorPullback.pullAlong L (prG i) (𝟙 S₀) (fun _ => eG) (fun _ => 1) (fun _ => eG') (hG i) rL)) b ∧
      LB.Gen.Corr L _ _ _ _ b (GeneratorPullback.finProdGen L (J := Fin j) (fun _ _ => eG) (fun _ _ => 1) (fun _ => rL)) := by
  refine ⟨⟨fun jN => res (linComb_comp_U_le_linComb_linComb_U (prG := prG) (eG' := eG') jN) ((GeneratorPullback.boxGen L prG (fun _ : PUnit => eG') (fun _ => 1)
      (fun i => GeneratorPullback.pullAlong L (prG i) (𝟙 S₀) (fun _ => eG) (fun _ => 1) (fun _ => eG') (hG i) rL)).s fun _ => jN)⟩, ?_, ?_⟩
  · unfold GeneratorPullback.MapsAt
    intro jN jL
    have H := hr (fun _ => jN) (fun _ => jL)
    have hO : eG' ⁻¹ᵁ ((L.LinComb prG fun _ => 1).U jN ⊓ (L.LinComb prG fun _ => 1).U jL) ≤
        ((L.LinComb prG fun _ => 1).LinComb (K := PUnit) (fun _ => eG') (fun _ => 1)).U (fun _ => jN) ⊓
          ((L.LinComb prG fun _ => 1).LinComb (K := PUnit) (fun _ => eG') (fun _ => 1)).U (fun _ => jL) := by
      intro x hx
      simp only [LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage,
        SetLike.mem_coe, Scheme.Hom.mem_preimage, TopologicalSpace.Opens.mem_inf] at hx ⊢
      exact ⟨fun _ => hx.1, fun _ => hx.2⟩
    have H2 := congrArg (res hO) H
    erw [linComb_unit_g_eq] at H2
    simp only [map_mul, sec_res_comp_algebraMap, res_self_lemma] at H2
    dsimp only
    erw [sec_res_comp_algebraMap]
    simp only [pow_one, zpow_one]
    exact H2
  · unfold LB.Gen.Corr GeneratorPullback.finProdGen
    intro j₁ j' c₁ c₂ hj
    have hk : ∀ k, j₁ k = j' (k, PUnit.unit) := fun k => hj k (k, PUnit.unit) (by simpa using hG k PUnit.unit)
    clear hj c₁ c₂ hr
    dsimp only
    unfold GeneratorPullback.boxGen GeneratorPullback.pullAlong
    dsimp only
    erw [sec_res_comp_algebraMap, map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro i _
    erw [sec_res_comp_algebraMap]
    exact (sec_res_comp_algebraMap _ _ _).trans ((res_pullU_id_eq_res'' _ _).trans
      ((res_congr_of_index_eq rL.s (funext fun k => by cases k; exact hk i) _ _).trans (sec_res_comp_algebraMap _ _ _).symm))

private theorem pullU_res_eq_res_pullU'' {X Y : Scheme.{0}} (r : Y ⟶ X) {U U' : X.Opens} (h' : U' ≤ U)
    (hh : r ⁻¹ᵁ U' ≤ r ⁻¹ᵁ U) (x : Γ(X, U)ˣ) : pullU r U' (res h' x) = res hh (pullU r U x) := by
  apply Units.ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

private theorem div_g_eq_res_mul_res_inv {X : Scheme.{0}} (A B : LB X) (p q : A.ι × B.ι) :
    (A.div B).g p q = res (inf_le_inf inf_le_left inf_le_left) (A.g p.1 q.1) *
      (res (inf_le_inf inf_le_right inf_le_right) (B.g p.2 q.2))⁻¹ := rfl

private theorem pull_g_eq_res_pullU {X Y : Scheme.{0}} (N : LB X) (e : Y ⟶ X) (a b : N.ι) :
    (N.pull e).g (fun _ => a) (fun _ => b) = res (linComb_unit_U_le N e a b) (pullU e (N.U a ⊓ N.U b) (N.g a b)) :=
  linComb_unit_g_eq N e a b

private theorem res_mul_rings_of_integers {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (a b : Γ(X, U)ˣ) :
    res h (a * b) = res h a * res h b := map_mul _ _ _

private theorem res_inv' {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ) :
    res h a⁻¹ = (res h a)⁻¹ := map_inv _ _

private theorem toFld_gm_res {X Y : Scheme.{0}} (r : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (hV : V ≤ r ⁻¹ᵁ U)
    (u : Γ(X, U)ˣ) (y : Y) (hy : y ∈ V) : gm (𝟙 Y) y V (res hV (pullU r U u)) = gm r y U u := by
  have hy' : r y ∈ U := hV hy
  have hy1 : (𝟙 Y : Y ⟶ Y) y ∈ V := hy
  unfold gm
  rw [dite_eq_left hy1, dite_eq_left hy']
  apply Units.ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, res, pullU]
  exact TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hV) y hy _

private theorem gm_id_res_eq' {Y : Scheme.{0}} {U V : Y.Opens} (hV : V ≤ U) (u : Γ(Y, U)ˣ) (y : Y) (hy : y ∈ V) :
    gm (𝟙 Y) y V (res hV u) = gm (𝟙 Y) y U u := by
  have hy1 : (𝟙 Y : Y ⟶ Y) y ∈ V := hy
  have hy2 : (𝟙 Y : Y ⟶ Y) y ∈ U := hV hy
  unfold gm
  rw [dite_eq_left hy1, dite_eq_left hy2]
  apply Units.ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, res, pullU]
  exact TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hV) y hy _

private theorem units_ext_of_gm_id_eq' {Y : Scheme.{0}} {V : Y.Opens} (a b : Γ(Y, V)ˣ)
    (H : ∀ y (hy : y ∈ V), gm (𝟙 Y) y V a = gm (𝟙 Y) y V b) : a = b := by
  apply Units.ext
  apply TopCat.Presheaf.section_ext Y.sheaf V
  intro y hy
  have e := congrArg Units.val (H y hy)
  have hy1 : (𝟙 Y : Y ⟶ Y) y ∈ V := hy
  unfold gm at e
  rw [dite_eq_left hy1] at e
  exact e

theorem square_res (hM' : M'.IsLB)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull f) (M.pull p)}
    {we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f') (M'.pull p')} {h : Fin j → (T' ⟶ T)}
    (hwe : we'.IsGen) (Q : BoxSquare w we we' h) (jNM : Fin j → M.ι) (jM' : M'.ι) (jL' jNL : Fin j → L.ι)
    (V : T'.Opens) (h₁ : V ≤ p' ⁻¹ᵁ (LB.div (LB.LinComb M pr (fun _ => 1)) M').U (jNM, jM'))
    (h₂ : V ≤ (LB.div (M'.pull p') ((LB.LinComb L prG (fun _ => 1)).pull f')).U (fun _ => jM', fun _ => jL'))
    (h₃ : ∀ i, V ≤ h i ⁻¹ᵁ (LB.div (M.pull p) (L.pull f)).U (fun _ => jNM i, fun _ => jNL i))
    (h₄ : V ≤ f' ⁻¹ᵁ (LB.div (LB.LinComb L prG (fun _ => 1)) (LB.LinComb L prG (fun _ => 1))).U (jNL, jL')) :
    res h₁ (pullU p' _ (w.s (jNM, jM'))) * res h₂ (we'.s (fun _ => jM', fun _ => jL')) =
      (∏ i, res (h₃ i) (pullU (h i) _ (we.s (fun _ => jNM i, fun _ => jNL i)))) *
        res h₄ (pullU f' _ ((idIso (LB.LinComb L prG (fun _ => 1))).s (jNL, jL'))) := by
  have hw2 := hwe
  unfold LB.Gen.IsGen at hw2
  have hV1 : V ≤ ((M'.pull p').div ((L.LinComb prG fun _ => 1).pull f')).U (fun _ => jM', fun _ => jNL) ⊓
      ((M'.pull p').div ((L.LinComb prG fun _ => 1).pull f')).U (fun _ => jM', fun _ => jL') := by
    intro x hx
    have a2 := h₂ hx
    have a4 := h₄ hx
    clear h₁ h₃ Q hwe hw2 h₂ h₄ hx
    simp only [LB.div, LB.pull, LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_inf, TopologicalSpace.Opens.mem_mk,
      TopologicalSpace.Opens.coe_mk, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, Scheme.Hom.mem_preimage, Set.mem_inter_iff] at a2 a4 ⊢
    refine ⟨⟨a2.1, ?_⟩, a2.1, ?_⟩
    · exact Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => a4.1 k
    · exact Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => a4.2 k
  have hg := congrArg (res hV1) (hw2 (fun _ => jM', fun _ => jNL) (fun _ => jM', fun _ => jL'))
  simp only [map_mul, sec_res_comp_algebraMap] at hg
  rw [div_g_eq_res_mul_res_inv] at hg
  dsimp only at hg
  rw [pull_g_eq_res_pullU] at hg
  erw [pull_g_eq_res_pullU] at hg
  simp only [map_mul, map_inv, sec_res_comp_algebraMap] at hg
  have hVp : V ≤ p' ⁻¹ᵁ M'.U jM' := fun y hy => (h₁ hy).2
  have hself : ∀ (k : V ≤ p' ⁻¹ᵁ (M'.U jM' ⊓ M'.U jM')),
      res k (pullU p' (M'.U jM' ⊓ M'.U jM') (M'.g jM' jM')) = 1 := by
    intro k
    have e1 := pullU_res_eq_res_pullU'' p' (le_inf le_rfl le_rfl : M'.U jM' ≤ M'.U jM' ⊓ M'.U jM') (fun y hy => ⟨hy, hy⟩)
      (M'.g jM' jM')
    rw [hM'.g_self jM', map_one] at e1
    exact (sec_res_comp_algebraMap hVp (show p' ⁻¹ᵁ M'.U jM' ≤ p' ⁻¹ᵁ (M'.U jM' ⊓ M'.U jM') from fun y hy => ⟨hy, hy⟩) _).symm.trans
      (by rw [← e1, map_one])
  have hX : ∀ k, res hV1 (res k (pullU p' (M'.U jM' ⊓ M'.U jM') (M'.g jM' jM'))) = 1 :=
    fun k => (sec_res_comp_algebraMap _ _ _).trans (hself _)
  erw [res_mul_rings_of_integers, res_inv'] at hg
  erw [hX] at hg
  rw [_root_.one_mul, eq_inv_mul_iff_mul_eq] at hg
  rw [← hg]
  refine (mul_left_comm _ _ _).trans ((mul_comm _ _).trans ?_)
  refine congrArg₂ (· * ·) ?_ ((sec_res_comp_algebraMap _ _ _).trans rfl)
  apply units_ext_of_gm_id_eq'
  intro y hy
  have c1 : ∀ i, pr i (p' ((𝟙 T' : T' ⟶ T') y)) ∈ M.U (jNM i) := fun i => Set.mem_iInter.1 (h₁ hy).1 i
  have c2 : p' ((𝟙 T' : T' ⟶ T') y) ∈ M'.U jM' := (h₁ hy).2
  have c3 : ∀ i, prG i (f' ((𝟙 T' : T' ⟶ T') y)) ∈ L.U (jNL i) := fun i => Set.mem_iInter.1 (h₄ hy).1 i
  have q := Q T' (𝟙 T') y jNM jM' jNL c1 c2 c3
  simp only [bw, Geo.Tor.gw, Category.id_comp] at q
  rw [map_mul, map_prod, toFld_gm_res _ _ _ _ hy, gm_id_res_eq' _ _ _ hy,
    Finset.prod_congr rfl (fun i _ => toFld_gm_res (h i) (h₃ i) _ y hy)]
  exact q

end GlobalTheory.PowUnif
end
end

