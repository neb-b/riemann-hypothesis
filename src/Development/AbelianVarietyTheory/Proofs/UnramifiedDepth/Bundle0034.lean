module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Statements.ChartPoints.ChartPt
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AppTopCharUnitOfTorusEndOf
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem appTop_charUnit_of_torusEndOf {S : Scheme.{0}} {X : Type} [AddCommGroup X] {h : X → X}
    {t : splitTorus S X ⟶ splitTorus S X} (ht : Out.TorusEndOf X h t) (χ : X) :
    t.left.appTop.hom (charUnit S X χ).val = (charUnit S X (h χ)).val := by
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, ht χ]

theorem qRel_iRel_equivariant : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G), ∀ (OE : Type) [CommRing OE] [StarRing OE] [Module OE D.toPre.X] (io : Out.RingAct G OE) (oD : D.OAct OE) (oA : A.OAct OE), U.OLinear OE oD oA io → ∀ (k : ℕ) (a : OE) (S : Type) [CommRing S] [Algebra R S], (∀ z y, QRel (U.gt k) S z y → QRel (U.gt k) S (z ≫ io.act a) (y ≫ oD.onB.act a)) ∧ ∀ χ χ' z, (∀ x, χ' (Multiplicative.ofAdd x) = χ (Multiplicative.ofAdd (star a • x))) → IRel (U.gt k) S χ z → IRel (U.gt k) S χ' (z ≫ io.act a) := by
  intro R _ _ I D A G _ _ U OE _ _ _ io oD oA hl k a S _ _
  have hG : ((Over.pullback (Out.thick R I k)).map (io.act a)).left ≫ (Out.fstG I k G).left =
      (Out.fstG I k G).left ≫ (io.act a).left :=
    GlobalTheory.SplitTorusPoints.map_left_fst (Out.thick R I k) (io.act a)
  refine ⟨?_, ?_⟩
  · rintro z y ⟨w, h1, h2⟩
    refine ⟨w ≫ ((Over.pullback (Out.thick R I k)).map (io.act a)).left, ?_, ?_⟩
    · rw [Over.comp_left, ← h1]
      exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) hG).trans (Category.assoc _ _ _).symm)
    · have hB : ((Over.pullback (Out.thick R I k)).map (oD.onB.act a)).left ≫
          (D.toPre.prBe I k).left = (D.toPre.prBe I k).left ≫ (oD.onB.act a).left :=
        GlobalTheory.SplitTorusPoints.map_left_fst (Out.thick R I k) (oD.onB.act a)
      have hq : ((Over.pullback (Out.thick R I k)).map (io.act a)).left ≫ (U.gt k).q.left =
          (U.gt k).q.left ≫ ((Over.pullback (Out.thick R I k)).map (oD.onB.act a)).left :=
        congrArg (·.left) (hl.q_lin k a)
      have hp : ((Over.pullback (Out.thick R I k)).map (io.act a)).left ≫ (U.gt k).pG.left =
          (U.gt k).pG.left ≫ (oD.onB.act a).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (D.toPre.prBe I k).left) hq).trans
          ((Category.assoc _ _ _).trans ((congrArg ((U.gt k).q.left ≫ ·) hB).trans
            (Category.assoc _ _ _).symm)))
      rw [Over.comp_left (g := oD.onB.act a), ← h2]
      exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) hp).trans (Category.assoc _ _ _).symm)
  · rintro χ χ' z hχ ⟨w, h1, h2⟩
    obtain ⟨t, ht, hi⟩ := hl.i_lin k a
    refine ⟨w ≫ t.left, fun x => ?_, ?_⟩
    · rw [hχ, ← h1, ← appTop_charUnit_of_torusEndOf ht x, Scheme.Hom.comp_appTop]
      rfl
    · have hi' : (U.gt k).i.left ≫ ((Over.pullback (Out.thick R I k)).map (io.act a)).left =
          t.left ≫ (U.gt k).i.left := congrArg (·.left) hi
      have hp : t.left ≫ (U.gt k).i.left ≫ (Out.fstG I k G).left =
          ((U.gt k).i.left ≫ (Out.fstG I k G).left) ≫ (io.act a).left :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (Out.fstG I k G).left) hi'.symm).trans
          ((Category.assoc _ _ _).trans ((congrArg ((U.gt k).i.left ≫ ·) hG).trans
            (Category.assoc _ _ _).symm)))
      rw [Over.comp_left, ← h2]
      exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) hp).trans (Category.assoc _ _ _).symm)

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterMemLatticeOfComul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private def latConv {C N : Type} [Field C] [Add N] (φ ψ : (N → C) →ₗ[C] C) :
    (N → C) →ₗ[C] C where
  toFun f := φ (fun x => ψ (fun y => f (x + y)))
  map_add' f g := by
    rw [← map_add (f := _)]; congr 1; funext x
    rw [Pi.add_apply, ← map_add (f := _)]; rfl
  map_smul' c f := by
    rw [RingHom.id_apply, ← map_smul]; congr 1; funext x
    rw [Pi.smul_apply, ← map_smul]; rfl

private theorem latConv_sum {C N : Type} [Field C] [Add N] (φ ψ : (N → C) →ₗ[C] C)
    {m : ℕ} (f : N → C) (g h : Fin m → N → C) (hf : ∀ x y, f (x + y) = ∑ i, g i x * h i y) :
    latConv φ ψ f = ∑ i, φ (g i) * ψ (h i) := by
  have h1 : ∀ x, (fun y => f (x + y)) = ∑ i, g i x • h i := by
    intro x; funext y; simp [hf, Finset.sum_apply]
  have h2 : (fun x => ψ (fun y => f (x + y))) = ∑ i, ψ (h i) • g i := by
    funext x; rw [h1]; simp [Finset.sum_apply, mul_comm]
  change φ (fun x => ψ (fun y => f (x + y))) = _
  rw [h2]; simp [mul_comm]

private theorem lat_bound {C V : Type} [Field C] [AddCommGroup V] [Module C V]
    (v : Valuation C NNReal) (S : Set V) {k : V} (hk : k ∈ Submodule.span C S) :
    ∃ M : NNReal, ∀ φ : V →ₗ[C] C, (∀ f ∈ S, v (φ f) ≤ 1) → v (φ k) ≤ M := by
  induction hk using Submodule.span_induction with
  | mem x hx => exact ⟨1, fun φ hφ => hφ x hx⟩
  | zero => exact ⟨0, fun φ _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, hM⟩ := hx
    obtain ⟨M', hM'⟩ := hy
    refine ⟨max M M', fun φ hφ => ?_⟩
    rw [map_add (f := _)]
    exact (v.map_add _ _).trans (max_le_max (hM φ hφ) (hM' φ hφ))
  | smul c x _ hx =>
    obtain ⟨M, hM⟩ := hx
    refine ⟨v c * M, fun φ hφ => ?_⟩
    rw [map_smul, smul_eq_mul, map_mul]
    gcongr
    exact hM φ hφ

private theorem lat_dual {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) {N : Type} (A : Submodule O (N → C)) (hfg : A.FG)
    (hsp : Submodule.span C (A : Set (N → C)) = ⊤) (k : N → C)
    (hk : ∀ φ : (N → C) →ₗ[C] C, (∀ f ∈ A, v (φ f) ≤ 1) → v (φ k) ≤ 1) : k ∈ A := by
  classical
  have := hv.hom_inj.isDomain
  have := ValuationRing.of_integers v hv
  have := hv.isFractionRing
  have : Module.Finite O A := Module.Finite.iff_fg.2 hfg
  have : Module.Flat O A := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro ⟨x, hxA⟩ hx
    rw [Submodule.mem_bot]
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hx
    have h' : ((a : O) • x : N → C) = 0 := congrArg Subtype.val ha
    rw [← algebraMap_smul C (a : O) x] at h'
    exact Subtype.ext ((smul_eq_zero.1 h').resolve_left
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2))
  have : Module.Free O A := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O A
  let w : Module.Free.ChooseBasisIndex O A → N → C := fun i => (b i : N → C)
  have hR : LinearIndependent O w := b.linearIndependent.map' A.subtype (Submodule.ker_subtype _)
  have hC : LinearIndependent C w := (LinearIndependent.iff_fractionRing O C).1 hR
  have hspR : Submodule.span O (Set.range w) = A := by
    have : Set.range w = A.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hspC : Submodule.span C (Set.range w) = ⊤ := by
    rw [← Submodule.span_span_of_tower O, hspR, hsp]
  let bC := Module.Basis.mk hC (by rw [hspC])
  have hb : ∀ i, bC i = w i := fun i => Module.Basis.mk_apply _ _ _
  have hco : ∀ i, ∀ f ∈ A, v (bC.coord i f) ≤ 1 := by
    intro i f hf
    rw [← hspR] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [← hb, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs <;> simp
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact v.map_add_le hx hy
    | smul c x _ hx =>
      rw [← algebraMap_smul C c x, map_smul, smul_eq_mul, map_mul]
      exact mul_le_one' (hv.map_le_one c) hx
  rw [← bC.sum_repr k]
  refine A.sum_mem fun i _ => ?_
  obtain ⟨o, ho⟩ := hv.exists_of_le_one (hk _ (hco i))
  have ho' : bC.repr k i = algebraMap O C o := ho.symm
  rw [ho', algebraMap_smul, hb]
  exact A.smul_mem _ (b i).2

theorem character_mem_lattice_of_comul : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (N : Type) [AddCommMonoid N] [Finite N] (A : Submodule O (N → C)), A.FG → Submodule.span C (A : Set (N → C)) = ⊤ → (∀ f ∈ A, ∃ (m : ℕ) (g h : Fin m → N → C), (∀ i, g i ∈ A) ∧ (∀ i, h i ∈ A) ∧ ∀ x y, f (x + y) = ∑ i, g i x * h i y) → (∀ f ∈ A, ∃ o : O, algebraMap O C o = f 0) → ∀ κ : N → C, κ 0 = 1 → (∀ x y, κ (x + y) = κ x * κ y) → κ ∈ A := by
  intro C _ v O _ _ hv N _ _ A hfg hsp hco h0 k hk0 hk
  refine lat_dual v hv A hfg hsp k fun φ hφ => ?_
  obtain ⟨M, hM⟩ := lat_bound v (A : Set (N → C)) (k := k) (by rw [hsp]; trivial)
  have hpow : ∀ n : ℕ, ∃ ψ : (N → C) →ₗ[C] C, (∀ f ∈ A, v (ψ f) ≤ 1) ∧ ψ k = φ k ^ n := by
    intro n
    induction n with
    | zero =>
      refine ⟨LinearMap.proj 0, fun f hf => ?_, by simpa using hk0⟩
      obtain ⟨o, ho⟩ := h0 f hf
      rw [LinearMap.proj_apply, ← ho]
      exact hv.map_le_one o
    | succ n ih =>
      obtain ⟨ψ, hψ, hψk⟩ := ih
      refine ⟨latConv ψ φ, fun f hf => ?_, ?_⟩
      · obtain ⟨m, g, h, hg, hh, hf⟩ := hco f hf
        rw [latConv_sum ψ φ f g h hf]
        refine v.map_sum_le fun i _ => ?_
        rw [map_mul]
        exact mul_le_one' (hψ _ (hg i)) (hφ _ (hh i))
      · rw [latConv_sum ψ φ k (fun _ : Fin 1 => k) (fun _ => k) (by simpa using hk)]
        simp [hψk, pow_succ]
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hlt
  obtain ⟨ψ, hψ, hψk⟩ := hpow n
  have := hM ψ hψ
  rw [hψk, map_pow] at this
  exact absurd hn (not_lt.2 this)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqZeroOfForallPairPointsValuationIntegersStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_forall_pair_points_valuationIntegers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (W : (PS O 1 d →ₐ[O] O) → Prop), (∀ f : PS O 1 d, (∀ φ, W φ → φ f = 0) → f = 0) → ∀ f : PS O 2 d, (∀ (Φ : PS O 2 d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O), (∀ u, Φ (ev (n := 2) ![pt O d 0] u) = φ u) → (∀ u, Φ (ev (n := 2) ![pt O d 1] u) = φ' u) → W φ → W φ' → Φ f = 0) → f = 0 := by
  first | exact @GlobalTheory.ChF.eq_zero_of_forall_pair_points_integers | exact GlobalTheory.ChF.eq_zero_of_forall_pair_points_integers | (intros; apply GlobalTheory.ChF.eq_zero_of_forall_pair_points_integers <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsGenericPointHom
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChTor

namespace GlobalTheory.ChTor

theorem exists_genericPoint_hom (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C]
    (hinj : Function.Injective (algebraMap O C)) (G : Over (Sp O)) [GrpObj G] (hsep : IsSeparated G.hom)
    (A : Over (Sp C)) [GrpObj A] (gen : A.left ⟶ G.left)
    (h : IsGrpPullback A G (spMap (algebraMap O C)) gen) :
    ∃ j : (algOver O O ⟶ G) →* Pts A, Function.Injective j ∧
      ∀ P z, z.left ≫ gen = spMap (algebraMap O C) ≫ P.left ↔ z = j P := by
  have hid : spMap (algebraMap O O) = 𝟙 (Sp O) := by
    simp [spMap]
  let e₀ : (Over.mk ((Over.mk (𝟙 (Sp C)) : Over (Sp C)).hom ≫ spMap (algebraMap O C)) : Over (Sp O)) ⟶ algOver O O :=
    Over.homMk (spMap (algebraMap O C)) (by
      change spMap (algebraMap O C) ≫ spMap (algebraMap O O) = 𝟙 _ ≫ spMap (algebraMap O C)
      rw [hid, Category.comp_id, Category.id_comp])
  have hw : ∀ P : algOver O O ⟶ G,
      (spMap (algebraMap O C) ≫ P.left) ≫ G.hom = 𝟙 (Sp C) ≫ spMap (algebraMap O C) := fun P => by
    have := Over.w (e₀ ≫ P)
    exact this
  let j₀ : (algOver O O ⟶ G) → Pts A := fun P =>
    Over.homMk (h.1.lift (spMap (algebraMap O C) ≫ P.left) (𝟙 (Sp C)) (hw P)) (h.1.lift_snd _ _ _)
  have hj : ∀ P, (j₀ P).left ≫ gen = spMap (algebraMap O C) ≫ P.left := fun P => h.1.lift_fst _ _ _
  have key : ∀ (P : algOver O O ⟶ G) (z : Pts A),
      z.left ≫ gen = spMap (algebraMap O C) ≫ P.left ↔ z = j₀ P := fun P z => by
    constructor
    · intro hz
      refine Over.OverMorphism.ext (h.1.hom_ext (hz.trans (hj P).symm) ?_)
      exact (Over.w z).trans (Over.w (j₀ P)).symm
    · rintro rfl
      exact hj P
  have hmul : ∀ P Q, j₀ (P * Q) = j₀ P * j₀ Q := fun P Q => by
    refine ((key _ _).1 ?_).symm
    have e := h.2 _ (j₀ P) (j₀ Q) (e₀ ≫ P) (e₀ ≫ Q) (hj P).symm (hj Q).symm
    rw [← MonObj.comp_mul] at e
    exact e.symm
  refine ⟨MonoidHom.mk' j₀ hmul, fun P Q hPQ => ?_, key⟩
  have hPQ' : j₀ P = j₀ Q := hPQ
  haveI : IsDomain O := hinj.isDomain _
  haveI : IsDominant (spMap (algebraMap O C)) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap O C)).2
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  refine Over.OverMorphism.ext ?_
  refine ext_of_isDominant_of_isSeparated (X := Sp O) G.hom ?_ (spMap (algebraMap O C)) ?_
  · exact (Over.w P).trans (Over.w Q).symm
  · exact (hj P).symm.trans (by rw [hPQ']; exact hj Q)

end GlobalTheory.ChTor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralCombinationOfMemHaO
section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem exists_integral_combination_of_mem_HaO :
    ∀ (T : Type) (r : T → ℕ) (n : ℕ) (V K C : Type) [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Field C] (e : K →+* C) (R : Subring C), (∀ x : V, e (algebraMap V K x) ∈ R) → ∀ (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T r n) C), P ∈ HaO r n C R cc isX a → ∃ (s : ℕ) (c : Fin s → C) (Q : Fin s → MvPolynomial (Letter T r n) K), (∀ j, c j ∈ R) ∧ (∀ j, Q j ∈ HaO r n K (algebraMap V K).range cc isX a) ∧ P = ∑ j, MvPolynomial.C (c j) * MvPolynomial.map e (Q j) := by
  intro T r n V K C _ _ _ _ _ _ _ e R hR cc isX a P hP
  classical
  let _ : Algebra K C := e.toAlgebra
  obtain ⟨hH, hO⟩ := hP
  obtain ⟨s, c, φ, hc, hφ⟩ := GlobalTheory.exists_integral_basis_linear_coordinates V K C R hR (P.support.image fun μ => P.coeff μ) (by
    intro x hx
    obtain ⟨μ, -, rfl⟩ := Finset.mem_image.mp hx
    exact hO μ)
  let Q : Fin s → MvPolynomial (Letter T r n) K := fun j =>
    ∑ μ ∈ P.support, MvPolynomial.monomial μ (φ j (P.coeff μ))
  have hQ : ∀ j μ, (Q j).coeff μ = φ j (P.coeff μ) := by
    intro j μ
    simp only [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]
  refine ⟨s, c, Q, hc, fun j => ⟨GlobalTheory.CoeffFunctional.mem_HHa_of_coeff_functional T r n K C (φ j) cc isX a P (Q j) (hQ j) hH, ?_⟩, ?_⟩
  · intro μ
    rw [hQ]
    by_cases h : μ ∈ P.support
    · exact (hφ _ (Finset.mem_image_of_mem _ h)).1 j
    · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]
      exact zero_mem _
  · ext μ
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, hQ]
    by_cases h : μ ∈ P.support
    · refine (hφ _ (Finset.mem_image_of_mem _ h)).2.trans ?_
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    · rw [MvPolynomial.notMem_support_iff.mp h]
      simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowerSeriesReadingGroupHomNilpotentCharts
section
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private def dbl (R : Type) [CommRing R] {S : Type} [CommRing S] [Algebra R S] (J : Ideal S) :
    Subalgebra R (S × S) :=
  AlgHom.equalizer ((Ideal.Quotient.mkₐ R J).comp (AlgHom.fst R S S))
    ((Ideal.Quotient.mkₐ R J).comp (AlgHom.snd R S S))

private theorem mem_dbl {R : Type} [CommRing R] {S : Type} [CommRing S] [Algebra R S] {J : Ideal S}
    {x : S × S} : x ∈ dbl R J ↔ x.1 - x.2 ∈ J := by
  rw [← Ideal.Quotient.eq]; rfl

private theorem exists_coord {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    {G' : Over (Spec (CommRingCat.of R))} [GrpObj G'] {d e : ℕ} {F : Fin d → PS R 2 d} {F' : Fin e → PS R 2 e}
    {X : Fam G d} {X' : Fam G' e} (h : NilChart G F X) (h' : NilChart G' F' X') (f : G ⟶ G') [IsMonHom f]
    (S : Type) [CommRing S] [Algebra R S] (a : Fin d → S) (ha : ∀ i, IsNilpotent (a i)) :
    ∃ b : Fin e → S, (∀ j, IsNilpotent (b j)) ∧ X S a ≫ f = X' S b := by
  let J : Ideal S := Ideal.span (Set.range a)
  have hJ : IsNilpotent J := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical ⟨(Set.finite_range a).toFinset, by simp [J]⟩, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ha i
  let ρ : dbl R J →ₐ[R] S := (AlgHom.fst R S S).comp (dbl R J).val
  let τ : dbl R J →ₐ[R] S := (AlgHom.snd R S S).comp (dbl R J).val
  let σ : S →ₐ[R] dbl R J := ((AlgHom.id R S).prod (AlgHom.id R S)).codRestrict _ (fun x => by
    simp [mem_dbl])
  have hker : IsNilpotent (RingHom.ker ρ) := by
    obtain ⟨n, hn⟩ := hJ
    refine ⟨n + 1, le_bot_iff.1 fun x hx => ?_⟩
    have h1 : x ∈ RingHom.ker ρ := Ideal.pow_le_self (Nat.succ_ne_zero n) hx
    have h2 : RingHom.ker ρ ≤ J.comap τ := fun y hy => by
      have h3 := mem_dbl.1 y.2
      have h4 : y.1.1 = 0 := hy
      rw [h4, zero_sub, neg_mem_iff] at h3
      exact h3
    have h5 := Ideal.le_comap_pow τ (n + 1) (Ideal.pow_right_mono h2 (n + 1) hx)
    rw [pow_succ, hn, zero_mul] at h5
    exact Subtype.ext (Prod.ext h1 h5)
  let a' : Fin d → dbl R J := fun i => ⟨(0, a i), mem_dbl.2 (by
    simpa using (Ideal.subset_span ⟨i, rfl⟩ : a i ∈ J))⟩
  have hnil : ∀ y : dbl R J, ρ y = 0 → IsNilpotent y := fun y hy => by
    obtain ⟨n, hn⟩ := hker
    exact ⟨n, by simpa [hn] using Ideal.pow_mem_pow (show y ∈ RingHom.ker ρ from hy) n⟩
  have ha' : ∀ i, IsNilpotent (a' i) := fun i => hnil _ rfl
  obtain ⟨b, hb, hz⟩ := h'.surj (dbl R J) S ρ σ (by ext; rfl) hker (X _ a' ≫ f) (by
    rw [← Category.assoc, h.nat _ _ ρ a' ha']
    have : (fun i => ρ (a' i)) = 0 := rfl
    rw [this, h.zero, MonObj.one_comp])
  refine ⟨fun j => τ (b j), fun j => (hnil _ (hb j)).map τ, ?_⟩
  rw [← h'.nat _ _ τ b (fun j => hnil _ (hb j)), ← hz, ← Category.assoc, h.nat _ _ τ a' ha']
  rfl

theorem exists_reads : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'] (d e : ℕ) (F : Fin d → PS R 2 d) (F' : Fin e → PS R 2 e) (X : Fam G d) (X' : Fam G' e), NilChart G F X → NilChart G' F' X' → ∀ f : G ⟶ G', IsMonHom f → ∃ φ : Fin e → PS R 1 d, Reads X X' f φ := by
  intro R _ G _ _ G' _ _ d e F F' X X' h h' f hf
  classical
  choose b hb hX using exists_coord h h' f
  let c : Fin e → ∀ (S : Type) [CommRing S] [Algebra R S], (Fin 1 × Fin d → S) → S :=
    fun j S _ _ a => if ha : ∀ i, IsNilpotent (a (0, i)) then b S (fun i => a (0, i)) ha j else 0
  have hc : ∀ j (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S']
      (φ : S →ₐ[R] S') (a : Fin 1 × Fin d → S), (∀ i, IsNilpotent (a i)) →
      φ (c j S a) = c j S' (fun i => φ (a i)) := by
    intro j S _ _ S' _ _ φ a ha
    have h1 : ∀ i, IsNilpotent (a (0, i)) := fun i => ha _
    have h2 : ∀ i, IsNilpotent (φ (a (0, i))) := fun i => (ha _).map φ
    simp only [c, dif_pos h1, dif_pos h2]
    refine congrFun (h'.inj S' (fun j => φ (b S _ h1 j)) (b S' _ h2) (fun j => (hb S _ h1 j).map φ)
      (hb S' _ h2) ?_) j
    rw [← hX, ← h'.nat _ _ φ _ (hb S _ h1), ← hX, ← Category.assoc, h.nat _ _ φ _ h1]
  choose φ hφ using fun j => GlobalTheory.exists_series_of_natural_on_nilpotent GlobalTheory.nEval_basic (c j) (hc j)
  have key : ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin d → S) (ha : ∀ i, IsNilpotent (a i)),
      b S a ha = fun j => nv (algebraMap R S) (φ j) ![a] := by
    intro S _ inst a ha
    funext j
    have h1 := hφ j S (fun q => a q.2) (fun q => ha _)
    simp only [c, dif_pos ha] at h1
    rw [h1, nv]
    have : (algebraMap R S).toAlgebra = inst := Algebra.algebra_ext _ _ fun _ => rfl
    rw [this]
    congr 1
    funext q
    obtain ⟨i, k⟩ := q
    fin_cases i
    rfl
  refine ⟨φ, fun j => ?_, fun S _ _ a ha => by rw [hX S a ha, key]⟩
  have h0 : ∀ i : Fin d, IsNilpotent ((0 : Fin d → R) i) := fun _ => IsNilpotent.zero
  have h1 : b R 0 h0 = 0 := h'.inj R _ _ (hb R 0 h0) (fun _ => IsNilpotent.zero) (by
    rw [← hX, h.zero, h'.zero, MonObj.one_comp])
  have h2 := hφ j R 0 (fun _ => IsNilpotent.zero)
  have h3 : c j R 0 = 0 := by
    exact (dif_pos h0).trans (congrFun h1 j)
  have h4 := (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; simp) : Ideal.span _ ≤ (⊥ : Ideal R))
    (evBasic_nEval_sub_coeff_mem (φ j) (0 : Fin 1 × Fin d → R) (fun _ => IsNilpotent.zero))
  rw [← h2, h3] at h4
  simpa using h4

end GlobalTheory.ChF
end
end

