module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0106

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemNonzeroLocusOfIsActOf
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoprimeTorsion

open CommutatorPairing

section General

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (T : Over S)

def chartPullLPow (n : ℕ) : ChartPull (LPow A L n T) (lbPow L n) (snd T A).left where
  idx j := fun _ => j 0
  le j y hy := mem_powChart.2 (Set.mem_iInter.1 hy 0)
  g y j j' hj hj' := by
    refine (gm_linComb L (fun _ : Fin 1 => (snd T A).left) (fun _ => (n : ℤ)) (𝟙 _) y j j' hj hj').trans
      (Eq.trans ?_ (gm_lbPow_g n (snd T A).left y _ _ (mem_powChart.2 (Set.mem_iInter.1 hj 0))
        (mem_powChart.2 (Set.mem_iInter.1 hj' 0))).symm)
    rw [Fin.prod_univ_one, Category.id_comp, zpow_natCast]

theorem nonzeroLocus_chartPullLPow (n : ℕ) (s : (lbPow L n).Sec) :
    nonzeroLocus (chartSec (chartPullLPow A L T n) s) = (snd T A).left ⁻¹ᵁ nonzeroLocus s :=
  nonzeroLocus_chartSec _ s fun _ J hJ => ⟨fun _ => J PUnit.unit, Set.mem_iInter.2 fun _ => mem_powChart.1 hJ⟩

def vanishing (a : ℤ) (E : Set (T ⊗ A).left) : Submodule Γ(T.left, ⊤) (SecM A L a T) where
  carrier := {f | ∀ y ∈ E, y ∉ nonzeroLocus (SecM.toSec A f)}
  add_mem' := by
    intro f f' hf hf' y hy h
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
    rcases Scheme.basicOpen_add_le _ (f.1 k) (f'.1 k) hk with h | h
    · exact hf y hy (Opens.mem_iSup.2 ⟨k, h⟩)
    · exact hf' y hy (Opens.mem_iSup.2 ⟨k, h⟩)
  zero_mem' := by
    intro y _ h
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
    exact (Scheme.basicOpen_zero _ _).le hk
  smul_mem' := by
    intro c f hf y hy h
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
    exact hf y hy (Opens.mem_iSup.2 ⟨k, ((Scheme.basicOpen_mul _ (liftHom A _ c) (f.1 k)).le hk).2⟩)

variable {A L T}

theorem mem_nonzeroLocus_of_isActOf (hL : L.IsLB) {a : ℤ} {θ : ThetaGrp A L a T} {s s' : LB.Sec (LPow A L a T)}
    (h : IsActOf A L a θ s s') {y : (T ⊗ A).left} (hy : y ∈ nonzeroLocus s') :
    (translT A θ.pt).left y ∈ nonzeroLocus s := by
  obtain ⟨k, hk, hu⟩ := (mem_nonzeroLocus s' y).1 hy
  obtain ⟨i, hi⟩ := exists_chart hL ((translPt A θ.pt).left y)
  obtain ⟨i₀, rfl⟩ : ∃ i₀ : L.ι, k = fun _ => i₀ := ⟨k 0, funext fun b => congrArg k (Subsingleton.elim _ _)⟩
  have hm : y ∈ LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] ![i₀, i] := Set.mem_iInter.2 fun b => by
    fin_cases b
    exacts [Set.mem_iInter.1 hk 0, hi]
  have hp := chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) ![i₀, i] hm
  have e := (gs_res (𝟙 _) y _ hm _).symm.trans ((congrArg (gs (𝟙 _) y _) (h ![i₀, i])).trans
    ((gs_mul (𝟙 _) y _ hm _ _).trans (congrArg (_ * ·) ((gs_res (𝟙 _) y _ hm _).trans
      (gs_pull (𝟙 _) (translT A θ.pt).left y _ hp _)))))
  have u := isUnit_of_mul_isUnit_right ((congrArg IsUnit e).mp hu)
  rw [Category.id_comp] at u
  exact (mem_nonzeroLocus_iff_pull s (translT A θ.pt).left y (k := fun _ => i) hp).2 u

end General

theorem dense_torsion (hA : AmpleSt) (hK : KerPowSt) (hI : IrredSt) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P : PolAV (Sp k)) {p : ℕ} (hp : p.Prime) :
    Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp k)) ⟶ P.A | ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ x ^ n = 1}, Set.range x.left) := by
  haveI : IsCommMonObj P.A := P.isAb.comm
  rw [dense_iff_inter_open]
  rintro U hU ⟨y₀, hy₀⟩
  by_contra hne
  obtain ⟨a, -, s, hs, hle, -⟩ := (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample).exists_affine_le
    (U := ⟨U, hU⟩) hy₀
  have gen : ∀ N : ℕ, 4 ≤ N → ∀ y : P.A.left, ∃ t : (lbPow P.L N).Sec, y ∈ nonzeroLocus t := fun N hN y => by
    obtain ⟨m, t, ht, -⟩ := veryAmple_lbPow hA k P N hN
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (ht.ge (Set.mem_univ y))
    exact ⟨t i, hi⟩
  obtain ⟨m, hm, hmp⟩ : ∃ m : ℕ, 4 ≤ m ∧ m.Coprime p :=
    ⟨p * 2 + 1, by have := hp.two_le; omega, by simp⟩
  obtain ⟨t, ht⟩ := gen m hm y₀
  let n := a * p + m
  have hn : 4 ≤ n := le_add_left hm
  have hnp : n.Coprime p := by simpa [n] using hmp
  let σ : (lbPow P.L n).Sec := secMul (secPow s p) t
  have hσ : nonzeroLocus σ = nonzeroLocus s ⊓ nonzeroLocus t := by
    rw [nonzeroLocus_secMul, nonzeroLocus_secPow s hp.one_le]
  let B := baseOver (Sp k)
  let β : ∀ T : Over (Sp k), T ⟶ B := fun T => Over.homMk T.hom (Category.comp_id _)
  let E : Set (B ⊗ P.A).left := ⋃ x ∈ {x : 𝟙_ (Over (Sp k)) ⟶ P.A | ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ x ^ n = 1},
    Set.range (lift (β _) x).left
  have hsnd : ∀ {T : Over (Sp k)} (x : T ⟶ P.A) (z : T.left), (snd B P.A).left ((lift (β T) x).left z) = x.left z :=
    fun x z => congrArg (fun q => q.left z) (lift_snd (β _) x)
  rcases hI k P n (Or.inr hn) (Nat.cast_ne_zero.2 (by omega)) (vanishing P.A P.L B n E) (fun θ r r' hr h y hy hy' => by
      refine h _ ?_ (mem_nonzeroLocus_of_isActOf P.isLB hr hy')
      obtain ⟨x, ⟨l, hl, hlp, hx⟩, z, rfl⟩ := Set.mem_iUnion₂.1 hy
      have hθ : θ.pt ^ n = 1 := (hK _ P n (by omega) B θ.pt).1 fun q =>
        ⟨⊤, trivial, exists_isGen_pull _ θ.φ θ.isGen _⟩
      refine Set.mem_iUnion₂.2 ⟨(β _ ≫ θ.pt) * x, ⟨n * l, by positivity, Nat.Coprime.mul_left hnp hlp, ?_⟩, z,
        (congrArg (fun q => q.left z) (lift_translT θ.pt (β _) x)).symm⟩
      rw [mul_pow, pow_mul, pow_mul', hx, ← MonObj.comp_pow, hθ, MonObj.comp_one, one_pow, one_pow,
        _root_.mul_one]) with h | h
  · have hmem : SecM.ofSec P.A (chartSec (chartPullLPow P.A P.L B n) σ) ∈ vanishing P.A P.L B n E := fun y hy hy' => by
      obtain ⟨x, hx, z, rfl⟩ := Set.mem_iUnion₂.1 hy
      have h₁ : (snd B P.A).left ((lift (β _) x).left z) ∈ nonzeroLocus σ :=
        (nonzeroLocus_chartPullLPow P.A P.L B n σ).le hy'
      rw [hsnd, hσ] at h₁
      exact hne ⟨_, hle h₁.1, Set.mem_iUnion₂.2 ⟨x, hx, z, rfl⟩⟩
    rw [h, Submodule.mem_bot] at hmem
    have h₂ : (lift (β _) (𝟙 P.A)).left y₀ ∈ nonzeroLocus (chartSec (chartPullLPow P.A P.L B n) σ) :=
      (nonzeroLocus_chartPullLPow P.A P.L B n σ).ge (show (snd B P.A).left _ ∈ nonzeroLocus σ by
        rw [hsnd, hσ]; exact ⟨hs, ht⟩)
    exact (hmem ▸ (vanishing P.A P.L B n Set.univ).zero_mem :
      SecM.ofSec P.A (chartSec (chartPullLPow P.A P.L B n) σ) ∈ vanishing P.A P.L B n Set.univ) _ trivial h₂
  · let z : (𝟙_ (Over (Sp k))).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
    obtain ⟨τ, hτ⟩ := gen n hn ((1 : 𝟙_ (Over (Sp k)) ⟶ P.A).left z)
    have hmem : SecM.ofSec P.A (chartSec (chartPullLPow P.A P.L B n) τ) ∈ vanishing P.A P.L B n E := by
      rw [h]; trivial
    refine hmem ((lift (β _) 1).left z) (Set.mem_iUnion₂.2 ⟨1, ⟨1, one_pos, by simp, one_pow _⟩, z, rfl⟩)
      ((nonzeroLocus_chartPullLPow P.A P.L B n τ).ge ?_)
    show (snd B P.A).left _ ∈ nonzeroLocus τ
    rw [hsnd]; exact hτ

end GlobalTheory.CoprimeTorsion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyObjMapOfFiniteEtaleCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ObjDescent

theorem isGrpPullback_id {S S₂ : Scheme.{0}} {G G' : Over S} {G₂ : Over S₂} [GrpObj G] [GrpObj G'] [GrpObj G₂]
    {q : S₂ ⟶ S} [Flat q] [Surjective q] {a : G₂.left ⟶ G.left} {c : G₂.left ⟶ G'.left}
    (h : IsGrpPullback G₂ G q a) (h' : IsGrpPullback G₂ G' q c) (φ : G.left ⟶ G'.left) [IsIso φ] (e : a ≫ φ = c)
    (w : φ ≫ G'.hom = G.hom ≫ 𝟙 S) : IsGrpPullback G G' (𝟙 S) φ := by
  refine ⟨IsPullback.of_horiz_isIso ⟨w⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let r := pullback.fst T.hom q
  have : Epi r := Flat.epi_of_flat_of_surjective _
  let T' : Over S₂ := Over.mk (pullback.snd T.hom q)
  have up : ∀ z : T ⟶ G, ∃ z' : T' ⟶ G₂, r ≫ z.left = z'.left ≫ a := fun z =>
    ⟨Over.homMk (h.1.lift (r ≫ z.left) (pullback.snd T.hom q)
      (by rw [Category.assoc, Over.w z]; exact pullback.condition)) (h.1.lift_snd _ _ _),
      (h.1.lift_fst _ _ _).symm⟩
  obtain ⟨x', hx'⟩ := up x
  obtain ⟨y', hy'⟩ := up y
  let R : Over.mk (T'.hom ≫ q) ⟶ T := Over.homMk r pullback.condition
  let R' : Over.mk (T'.hom ≫ q) ⟶ Over.mk (T.hom ≫ 𝟙 S) :=
    Over.homMk r ((congrArg (r ≫ ·) (Category.comp_id T.hom)).trans pullback.condition)
  have e₁ := h.2 T' x' y' (R ≫ x) (R ≫ y) hx' hy'
  have e₂ := h'.2 T' x' y' (R' ≫ x₀) (R' ≫ y₀)
    (by show r ≫ x₀.left = _; rw [hx, ← Category.assoc, hx', Category.assoc, e])
    (by show r ≫ y₀.left = _; rw [hy, ← Category.assoc, hy', Category.assoc, e])
  rw [← MonObj.comp_mul] at e₁ e₂
  rw [← cancel_epi r, ← Category.assoc]
  refine e₂.trans ?_
  rw [← e, ← Category.assoc]
  exact congrArg (· ≫ φ) e₁.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {b : Base l B} {b' : Base l B'} {b'' : Base l B''}
  {S S₂ : Scheme.{0}} {s : S ⟶ Sp B} {s' : S ⟶ Sp B'} {s'' : S₂ ⟶ Sp B''}
  {u : Obj D l b s} {ob : Obj D l b' s'} {ob₂ : Obj D l b'' s''} {q : S₂ ⟶ S}

theorem exists_congr {q' : S₂ ⟶ S} (e : q = q') (m : ObjMap ob₂ ob q) :
    ∃ m' : ObjMap ob₂ ob q', m'.toSABMap.φ = m.toSABMap.φ := by
  subst e
  exact ⟨m, rfl⟩

theorem comp_eq_of_comp_eq (hL : Out.Laws) (m : ObjMap ob₂ ob q) (n : ObjMap ob₂ u q) {Z : Scheme.{0}}
    (g₁ g₂ : Z ⟶ ob₂.t.G.left) (h : g₁ ≫ m.toSABMap.φ = g₂ ≫ m.toSABMap.φ) :
    g₁ ≫ n.toSABMap.φ = g₂ ≫ n.toSABMap.φ := by
  have hp : (g₁ ≫ ob₂.t.G.hom) ≫ q = (g₂ ≫ ob₂.t.G.hom) ≫ q := by
    rw [Category.assoc, Category.assoc, ← m.cart.1.w, ← Category.assoc, h, Category.assoc]
  obtain ⟨o, ⟨m₁⟩⟩ := obj_pull E H D l B'' B'' b'' b'' (RingHom.id _) S₂ Z s'' ((g₁ ≫ ob₂.t.G.hom) ≫ s'')
    (g₁ ≫ ob₂.t.G.hom) rfl rfl ((Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm)) ob₂
  obtain ⟨k, hk⟩ := ObjComp.objMap_comp m m₁
  obtain ⟨k', hk'⟩ := exists_congr hp k
  obtain ⟨m₂, hm₂⟩ := ObjComp.objMap_cancel m k'
  obtain ⟨n₁, hn₁⟩ := ObjComp.objMap_comp n m₁
  obtain ⟨n₁', hn₁'⟩ := exists_congr hp n₁
  obtain ⟨n₂, hn₂⟩ := ObjComp.objMap_comp n m₂
  have e := obj_rigid_of_pol hL obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ _ _ _ _ u o _
    n₁'.toSABMap n₂.toSABMap fun a => ⟨_, n₁'.eta a, n₂.eta a⟩
  rw [hn₁', hn₁, hn₂] at e
  rw [hk', hk] at hm₂
  let σ := m₁.cart.1.lift g₁ (𝟙 Z) (Category.id_comp _).symm
  have h₁ : σ ≫ m₁.toSABMap.φ = g₁ := m₁.cart.1.lift_fst _ _ _
  have h₀ : σ ≫ o.t.G.hom = 𝟙 Z := m₁.cart.1.lift_snd _ _ _
  have h₂ : σ ≫ m₂.toSABMap.φ = g₂ := by
    apply m.cart.1.hom_ext
    · rw [Category.assoc]
      refine (congrArg (σ ≫ ·) hm₂.symm).trans ?_
      rw [← Category.assoc, h₁, h]
    · rw [Category.assoc, m₂.cart.1.w, ← Category.assoc, h₀, Category.id_comp]
  refine (congrArg (· ≫ n.toSABMap.φ) h₁).symm.trans (Eq.trans ?_ (congrArg (· ≫ n.toSABMap.φ) h₂))
  exact (Category.assoc _ _ _).trans ((congrArg (σ ≫ ·) e).trans (Category.assoc _ _ _).symm)

variable [Flat q] [Surjective q] [QuasiCompact q]

theorem effectiveEpi (m : ObjMap ob₂ ob q) : EffectiveEpi m.toSABMap.φ := by
  have : Flat m.toSABMap.φ := MorphismProperty.of_isPullback m.cart.1.flip inferInstance
  have : Surjective m.toSABMap.φ := MorphismProperty.of_isPullback m.cart.1.flip inferInstance
  have : QuasiCompact m.toSABMap.φ := MorphismProperty.of_isPullback m.cart.1.flip inferInstance
  infer_instance

theorem exists_fac (hL : Out.Laws) (m : ObjMap ob₂ ob q) (n : ObjMap ob₂ u q) :
    ∃ φ : ob.t.G.left ⟶ u.t.G.left, m.toSABMap.φ ≫ φ = n.toSABMap.φ :=
  have := effectiveEpi m
  ⟨EffectiveEpi.desc m.toSABMap.φ n.toSABMap.φ (comp_eq_of_comp_eq hL m n), EffectiveEpi.fac _ _ _⟩

theorem nonempty_objMap_id (hL : Out.Laws) (m : ObjMap ob₂ ob q) (n : ObjMap ob₂ u q) :
    Nonempty (ObjMap ob u (𝟙 S)) := by
  obtain ⟨φ, hφ⟩ := exists_fac hL m n
  obtain ⟨ψ, hψ⟩ := exists_fac hL n m
  have := effectiveEpi m
  have := effectiveEpi n
  have : Epi q := Flat.epi_of_flat_of_surjective _
  have : IsIso φ := ⟨ψ, by rw [← cancel_epi m.toSABMap.φ, ← Category.assoc, hφ, hψ, Category.comp_id],
    by rw [← cancel_epi n.toSABMap.φ, ← Category.assoc, hψ, hφ, Category.comp_id]⟩
  have w : φ ≫ u.t.G.hom = ob.t.G.hom ≫ 𝟙 S := by
    rw [← cancel_epi m.toSABMap.φ, ← Category.assoc, hφ, Category.comp_id, m.cart.1.w, n.cart.1.w]
  have gp : IsGrpPullback ob.t.G u.t.G (𝟙 S) φ := isGrpPullback_id m.cart n.cart φ hφ w
  have hact : ∀ a, (ob.t.act.act a).left ≫ φ = φ ≫ (u.t.act.act a).left := fun a => by
    rw [← cancel_epi m.toSABMap.φ, ← Category.assoc, ← m.act, Category.assoc, hφ, n.act, ← Category.assoc, hφ]
  have hiso : LBIso ob.t.PP.L (u.t.PP.L.pull φ) := by
    have h₁ := ob.t.PP.isLB
    have h₂ := pull_isLB u.t.PP.isLB φ
    have hN := LB.isLB_div h₂ h₁
    have cN : CechPic.cls _ hN = CechPic.pull φ (CechPic.cls _ u.t.PP.isLB) - CechPic.cls _ h₁ :=
      CechPic.cls_div h₂ h₁ hN
    have cl : ∀ {t : SAB H S} (k : SABMap ob₂.t t q),
        CechPic.cls _ ob₂.t.PP.isLB = CechPic.pull k.φ (CechPic.cls _ t.PP.isLB) := fun {t} k => by
      obtain ⟨w, hw, -⟩ := k.lin
      exact (CechPic.cls_eq_iff _ (pull_isLB t.PP.isLB _)).2 ⟨w, hw⟩
    have z : ∀ t : SAB H S, CechPic.pull (eSec t.G) (CechPic.cls _ t.PP.isLB) = 0 := fun t =>
      (CechPic.cls_eq_zero_iff (pull_isLB t.PP.isLB _)).2 ⟨_, t.PP.rigGen⟩
    refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange hL.globalFns S S₂ q ob.t.G _ (ObjDim.isAbelianScheme ob) hN inferInstance inferInstance
      inferInstance ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
      ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
    · have he : eSec ob.t.G ≫ φ = 𝟙 S ≫ eSec u.t.G := (cubeMapOf gp).e_comm
      rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, z, he, Category.id_comp, z, sub_zero]
    · rw [CechPic.cls_pull hN, cN, ← m.cart.1.isoPullback_inv_fst, CechPic.pull_comp, map_sub, ← CechPic.pull_comp,
        hφ, ← cl, ← cl, sub_self, map_zero]
  obtain ⟨k, hk⟩ := exists_sabMap_of_isProper_of_lbIso hL.globalFns E H S S u.t ob.t (𝟙 S) φ u.proper gp hiso hact
  have key : ∀ (σ₂ : S₂ ⟶ ob₂.t.G.left) (σ : S ⟶ ob.t.G.left) (τ : S ⟶ u.t.G.left),
      σ₂ ≫ m.toSABMap.φ = q ≫ σ → σ₂ ≫ n.toSABMap.φ = q ≫ τ → σ ≫ k.φ = 𝟙 S ≫ τ := fun σ₂ σ τ h₁ h₂ => by
    rw [← cancel_epi q, hk, Category.id_comp, ← Category.assoc, ← h₁, ← h₂, Category.assoc, hφ]
  exact ⟨⟨k, fun a => key _ _ _ (m.eta a) (n.eta a), fun a => key _ _ _ (m.etaA a) (n.etaA a)⟩⟩

end GlobalTheory.ObjDescent

namespace GlobalTheory

theorem nonempty_objMap_of_finite_etale_cover : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (X S S₂ : Scheme.{0}) (s : X ⟶ Sp B) (s' : S ⟶ Sp B') (s'' : S₂ ⟶ Sp B'') (u : Obj D l b s) (ob : Obj D l b' s') (ob₂ : Obj D l b'' s'') (q : S₂ ⟶ S) (f : S ⟶ X), (IsReduced S ∨ IsLocallyNoetherian S) → IsFinite q → Etale q → Surjective q → Nonempty (ObjMap ob₂ ob q) → Nonempty (ObjMap ob₂ u (q ≫ f)) → Nonempty (ObjMap ob u f) := by
  intro hL _ E _ _ _ H D l B B' B'' _ _ _ b b' b'' X S S₂ s s' s'' u ob ob₂ q f _ _ _ _ ⟨m⟩ ⟨n⟩
  obtain ⟨u', ⟨p⟩⟩ := obj_pull E H D l B B b b (RingHom.id _) X S s (f ≫ s) f rfl rfl
    ((Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm)) u
  obtain ⟨n', -⟩ := ObjComp.objMap_cancel p n
  obtain ⟨k⟩ := ObjDescent.nonempty_objMap_id hL m n'
  obtain ⟨k', -⟩ := ObjComp.objMap_comp p k
  obtain ⟨k'', -⟩ := ObjDescent.exists_congr (Category.id_comp f) k'
  exact ⟨k''⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
section
noncomputable section

namespace GlobalTheory.ModelCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ObjPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

section Obj

variable {B : Type} [CommRing B] {b : Base l B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {f : S' ⟶ S}

def objOfSABMap (o : Obj D l b s) {t' : SAB H S'} (m : SABMap t' o.t f) : Obj D l b (f ≫ s) :=
  have hL : LBIso t'.PP.L (o.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hpr := o.proper
  have hp := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally
    S S' o.t.G t'.G f m.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB
    (AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi) m.cart hL
  { t := t'
    proper := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hpr
    ample := hp.2.1 o.ample
    ktriv := hp.2.2 o.ktriv
    eta := fun a => GlobalTheory.ObjPull.secPull m.cart (o.eta a)
    eta_add := fun a c => by rw [o.eta_add, map_mul]
    eta_ker := fun a ha => by rw [o.eta_ker a ha, map_one]
    etaA := fun a => GlobalTheory.ObjPull.secPull m.cart (o.etaA a)
    etaA_add := fun a c => by rw [o.etaA_add, map_mul]
    etaA_ker := fun a => by rw [o.etaA_ker a, map_one]
    geom := fun k _ _ x β hx => by
      obtain ⟨hdet, I, hI, hA, hM⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hx])
      refine ⟨fun τ => ?_, tateMove (pushEquiv m.cart (Over.mk x)) (fun c g => ?_) (fun n g g' c hc => ?_) I,
        hI, fun a => ?_, fun a ha => ?_⟩
      · rw [GlobalTheory.LiePull.lieMult_pull _ S S' o.t.G t'.G f m.cm.F o.t.act t'.act m.cart m.act k x τ,
          GlobalTheory.LiePull.lieMult_pull _ S S' o.t.G t'.G f m.cm.F o.t.act t'.act m.cart m.act k x τ]
        exact hdet τ
      · apply Over.OverMorphism.ext
        show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
        rw [Category.assoc, m.act, Category.assoc]
      · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' o.t.G t'.G f m.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB
          m.cart hL (Over.mk x) n g g' _ _ _ rfl rfl).2 hc
      · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull m.cart _ _).trans (hA a))
      · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull m.cart _ _).trans (hM a ha)) }

def objMapOfSABMap (o : Obj D l b s) {t' : SAB H S'} (m : SABMap t' o.t f) : ObjMap (objOfSABMap o m) o f :=
  ⟨m, fun _ => secPull_left m.cart _, fun _ => secPull_left m.cart _⟩

theorem sec_eq_secPull {t : SAB H S} {t' : SAB H S'} (m : SABMap t' t f) {e : 𝟙_ (Over S) ⟶ t.G}
    {e' : 𝟙_ (Over S') ⟶ t'.G} (h : e'.left ≫ m.φ = f ≫ e.left) : e' = GlobalTheory.ObjPull.secPull m.cart e := by
  apply Over.OverMorphism.ext
  apply m.cart.1.hom_ext
  · exact h.trans (secPull_left m.cart _).symm
  · rw [Over.w, Over.w]

end Obj

section Model

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

variable (Y : Model Xo c β)

end Model

section Push

variable {X : Scheme.{0}} {G : Over X} {L : LB G.left}

end Push

end GlobalTheory.ModelCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticDatumTorsionLevel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SiegUnram

open GlobalTheory.FamRep

section Group

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left}



end Group

variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
  {s' : S' ⟶ Sp o}

theorem locallyOfFiniteType_of_isQProjOver (h : IsQProjOver s) : LocallyOfFiniteType s := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have := isProper_str o N
  infer_instance

end GlobalTheory.SiegUnram
end
end

