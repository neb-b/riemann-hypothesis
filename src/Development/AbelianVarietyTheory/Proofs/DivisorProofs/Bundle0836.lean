module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0778
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumEntireAndNormalizedJetsAlgebraic

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeEigenfunctionOfLiftableElement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.LevelRows

variable {D : D7}

theorem levelType_eigenfunction_of_liftable_element {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {P : LevelP L.Pg L.r ℂ} {F : GA D V → ℂ} (hF : HasType V β (withP L P) F) (p : P.H)
    (hex : ∃ κ, IsLevelLift V β L p.1 κ) :
    actG0 V β L p.1 F = fun h => ((P.chi p : ℂˣ) : ℂ) * F h := by
  have hκ : IsLevelLift V β L p.1 hex.choose := hex.choose_spec
  have hp : rTup β L (finE V hex.choose) ∈ P.H := by rw [hκ.2.2]; exact p.2
  have hmem : hex.choose ∈ levG V β (withP L P) := ⟨hκ.1, hκ.2.1, hp⟩
  have hc : levChi V β (withP L P) hex.choose = ((P.chi p : ℂˣ) : ℂ) * levChi V β (flagL L) hex.choose := by
    unfold levChi
    rw [levFn_withP, extendOne_of_mem _ hp, Units.val_mul]
    congr 3
    exact Subtype.ext hκ.2.2
  have ha := levChi_ne_zero (β := β) (flagL L) hex.choose
  funext h
  unfold actG0
  rw [dite_eq_left hex, hF _ hmem h, hc]
  field_simp

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_lift_of_ne_zero (R : RealDat D A Ks) (hinj : Function.Injective R.HE.e) (hg : R.models_gE)
    {x : R.HE.H} (hx : x ≠ 0) (g : G) : ∃ κ, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) κ := by
  by_contra hk
  apply hx
  have h0 : R.gE g x = 0 := by
    apply hinj
    rw [hg g x, map_zero]
    ext v h
    show actG0 _ _ _ _ _ h = 0
    unfold actG0
    rw [dite_eq_right hk]
    rfl
  have : R.gE g⁻¹ (R.gE g x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, h0, map_zero]

theorem rowsOfLevel_of_models (R : RealDat D A Ks) (F : Face D A) (hE : R.models_HE) (hg : R.models_gE) :
    GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows.RowsOfLevel R F := by
  intro b x
  have hx : R.HE.e x ∈ R.EEat R.triv := hE.2.1 ▸ LinearMap.mem_range_self _ x
  unfold RealDat.EEat at hx ⊢
  rw [mem_goodPart, GlobalTheory.MultMem.mem_mult_iff] at hx ⊢
  constructor
  · rintro ⟨h1, -⟩ g
    by_cases h0 : x = 0
    · simp [h0]
    apply hE.1
    rw [hg, map_smul]
    ext v h
    have hmem : R.eG g ∈ (R.levR F b).H := by
      show R.eG.symm (R.eG g) ∈ (F.lvl b).P
      rw [MulEquiv.symm_apply_apply]; exact g.2
    have h2 := levelType_eigenfunction_of_liftable_element (V := Yc D 0) (β := R.βY 0) (L := R.dat0 R.triv) (P := R.levR F b)
      (F := R.HE.e x v) (fun κ hκ h => h1.lev v κ hκ h) ⟨R.eG g, hmem⟩ (exists_lift_of_ne_zero R hE.1 hg h0 g)
    have h3 : (R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P) ⟨R.eG g, hmem⟩ = g :=
      Subtype.ext (R.eG.symm_apply_apply g)
    refine (congrFun h2 h).trans ?_
    show D.what₂.embLL (((F.lvl b).ψ ((R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P) ⟨R.eG g, hmem⟩) : D.what₂.LLˣ) : D.what₂.LL) * _ = _
    rw [h3]
    rfl
  · intro h
    refine ⟨⟨hx.1.aut, hx.1.cusp, fun v => ?_, hx.1.equiv, hx.1.cont⟩, hx.2⟩
    have hP : IsPLevel (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.levR F b) (R.HE.e x v) := by
      refine ⟨fun κ hκ y => hx.1.lev v κ hκ y, fun p => ?_⟩
      have h1 := congrArg (fun z => R.HE.e z v) (h ⟨R.eG.symm p.1, p.2⟩)
      simp only [hg _ x, map_smul] at h1
      have h2 : R.eG (R.eG.symm p.1) = p.1 := R.eG.apply_symm_apply p.1
      rw [h2] at h1
      exact h1
    exact fun κ hκ y => hP.hasType κ hκ y

end GlobalTheory.LevelRows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlueOfOpenCoverCocycle
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PicGlue

variable {X : Scheme.{0}} {Ix : Type}

def sigmaGlue (W : Ix → X.Opens) (L : Ix → LB X) (w : ∀ i k, Cmp (W i ⊓ W k) (L i) (L k))
    (hL : ∀ i, IsOn (W i) (L i)) : LB X :=
  ⟨Σ i, (L i).ι, fun p ↦ (L p.1).U p.2,
    fun p q ↦ res (le_inf (inf_le_inf ((hL p.1).le p.2) ((hL q.1).le q.2)) le_rfl) (w p.1 q.1 p.2 q.2)⟩

theorem gm_sigmaGlue_g (W : Ix → X.Opens) (L : Ix → LB X) (w : ∀ i k, Cmp (W i ⊓ W k) (L i) (L k))
    (hL : ∀ i, IsOn (W i) (L i)) (x : X) (p q : (sigmaGlue W L w hL).ι)
    (hp : x ∈ (L p.1).U p.2) (hq : x ∈ (L q.1).U q.2) :
    gm (𝟙 X) x _ ((sigmaGlue W L w hL).g p q) = gm (𝟙 X) x _ (w p.1 q.1 p.2 q.2) :=
  gm_res (𝟙 X) x _ (show x ∈ (L p.1).U p.2 ⊓ (L q.1).U q.2 from ⟨hp, hq⟩) _

theorem lb_glue : ∀ (X : Scheme.{0}) (Ix : Type) (W : Ix → X.Opens) (L : Ix → LB X) (w : ∀ i k, Cmp (W i ⊓ W k) (L i) (L k)), (∀ x, ∃ i, x ∈ W i) → (∀ i, IsOn (W i) (L i)) → (∀ i k, IsoOn (W i ⊓ W k) (L i) (L k) (w i k)) → (∀ (i j k : Ix) (x : X) (a : (L i).ι) (b : (L j).ι) (c : (L k).ι), x ∈ (L i).U a → x ∈ (L j).U b → x ∈ (L k).U c → gm (𝟙 X) x _ (w i j a b) * gm (𝟙 X) x _ (w j k b c) = gm (𝟙 X) x _ (w i k a c)) → ∃ N : LB X, N.IsLB ∧ ∀ i, ∃ v : Cmp (W i) N (L i), IsoOn (W i) N (L i) v := by
  intro X Ix W L w hW hL hiso hcoc
  have hdiag : ∀ i (a : (L i).ι) (x : X), x ∈ (L i).U a → gm (𝟙 X) x _ (w i i a a) = 1 :=
    fun i a x ha ↦ mul_eq_left.1 (hcoc i i i x a a a ha ha ha)
  have hgi : ∀ i (x : X) (b b' : (L i).ι), x ∈ (L i).U b → x ∈ (L i).U b' → x ∈ W i →
      gm (𝟙 X) x _ ((L i).g b b') = gm (𝟙 X) x _ (w i i b b') := by
    intro i x b b' hb hb' hx
    have h1 := hiso i i x ⟨hx, hx⟩ b b b b' hb hb hb hb'
    have h2 : gm (𝟙 X) x _ ((L i).g b b) = 1 := mul_eq_left.1 ((hL i).coc x b b b hb hb hb)
    rw [hdiag i b x hb, _root_.one_mul, h2, _root_.one_mul] at h1
    exact h1
  have hg := gm_sigmaGlue_g W L w hL
  refine ⟨sigmaGlue W L w hL, ⟨?_, ?_, ?_⟩, fun i ↦ ⟨fun p b ↦ res (le_inf (le_inf
    (inf_le_right.trans (inf_le_left.trans ((hL p.1).le p.2))) inf_le_left) inf_le_right) (w p.1 i p.2 b), ?_⟩⟩
  · refine eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 ?_
    obtain ⟨i, hi⟩ := hW x
    obtain ⟨a, ha⟩ := (hL i).cov x hi
    exact ⟨⟨i, a⟩, ha⟩
  · intro p
    refine unit_ext fun x hx ↦ ?_
    rw [gm_res (𝟙 X) x _ hx, map_one, hg x p p hx hx, hdiag p.1 p.2 x hx]
  · intro p q r
    refine unit_ext fun x hx ↦ ?_
    rw [map_mul, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx,
      hg x p q hx.1.1 hx.1.2, hg x q r hx.1.2 hx.2, hg x p r hx.1.1 hx.2]
    exact hcoc _ _ _ x _ _ _ hx.1.1 hx.1.2 hx.2
  · intro x hx p p' b b' hp hp' hb hb'
    beta_reduce
    erw [gm_res (𝟙 X) x _ (show x ∈ W i ⊓ ((sigmaGlue W L w hL).U p ⊓ (L i).U b) from ⟨hx, hp, hb⟩),
      gm_res (𝟙 X) x _ (show x ∈ W i ⊓ ((sigmaGlue W L w hL).U p' ⊓ (L i).U b') from ⟨hx, hp', hb'⟩),
      hg x p p' hp hp', hgi i x b b' hb hb' hx, hcoc _ _ _ x _ _ _ hp hb hb', hcoc _ _ _ x _ _ _ hp hp' hb']

end GlobalTheory.PicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullOfIsLineBundleIsoOnOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem isoOn_gm {X Z : Scheme.{0}} {W : X.Opens} {L M : LB X} {w : Cmp W L M} (hw : IsoOn W L M w) (r : Z ⟶ X)
    (y : Z) {a a' : L.ι} {b b' : M.ι} (h0 : r y ∈ W) (ha : r y ∈ L.U a) (ha' : r y ∈ L.U a') (hb : r y ∈ M.U b)
    (hb' : r y ∈ M.U b') :
    gm r y _ (w a b) * gm r y _ (M.g b b') = gm r y _ (L.g a a') * gm r y _ (w a' b') := by
  have h1 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ W ⊓ (L.U a ⊓ M.U b) := inf_le_left
  have h2 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ M.U b ⊓ M.U b' :=
    le_inf (inf_le_left.trans (inf_le_right.trans inf_le_right)) (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have h3 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ L.U a ⊓ L.U a' :=
    le_inf (inf_le_left.trans (inf_le_right.trans inf_le_left)) (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have h4 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ W ⊓ (L.U a' ⊓ M.U b') := inf_le_right
  have key : ∀ (T : Scheme.{0}) (f : T ⟶ X) (t : T), f t ∈ (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) →
      gm f t _ (res h1 (w a b) * res h2 (M.g b b')) = gm f t _ (w a b) * gm f t _ (M.g b b') ∧
      gm f t _ (res h3 (L.g a a') * res h4 (w a' b')) = gm f t _ (L.g a a') * gm f t _ (w a' b') :=
    fun T f t ht ↦ ⟨(map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f t h1 ht _) (gm_res f t h2 ht _)),
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f t h3 ht _) (gm_res f t h4 ht _))⟩
  have e : res h1 (w a b) * res h2 (M.g b b') = res h3 (L.g a a') * res h4 (w a' b') :=
    unit_ext fun x hx ↦ (key X (𝟙 X) x hx).1.trans ((hw x (h1 hx).1 a a' b b' (h3 hx).1 (h3 hx).2 (h2 hx).1 (h2 hx).2).trans
      (key X (𝟙 X) x hx).2.symm)
  have hm : r y ∈ (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) := ⟨⟨h0, ha, hb⟩, ⟨h0, ha', hb'⟩⟩
  exact (key Z r y hm).1.symm.trans ((congrArg (gm r y _) e).trans (key Z r y hm).2)

theorem lbIso_pull_of_isoOn (X Z : Scheme.{0}) (W : X.Opens) (L M : LB X) (w : Cmp W L M) (r : Z ⟶ X)
    (hw : IsoOn W L M w) (hr : ∀ z, r z ∈ W) : LBIso (L.pull r) (M.pull r) := by
  have le : ∀ p : (PUnit → M.ι) × (PUnit → L.ι), (M.pull r).U p.1 ⊓ (L.pull r).U p.2 ≤
      r ⁻¹ᵁ (W ⊓ (L.U (p.2 PUnit.unit) ⊓ M.U (p.1 PUnit.unit))) :=
    fun p y hy ↦ ⟨hr y, mem_pull.1 hy.2, mem_pull.1 hy.1⟩
  refine ⟨⟨fun p ↦ (res (le p) (pullU r _ (w (p.2 PUnit.unit) (p.1 PUnit.unit))))⁻¹⟩, fun p q ↦ unit_ext fun y hy ↦ ?_⟩
  have val : ∀ p : (PUnit → M.ι) × (PUnit → L.ι), y ∈ (M.pull r).U p.1 ⊓ (L.pull r).U p.2 →
      gm (𝟙 Z) y _ (res (le p) (pullU r _ (w (p.2 PUnit.unit) (p.1 PUnit.unit))))⁻¹ =
        (gm r y _ (w (p.2 PUnit.unit) (p.1 PUnit.unit)))⁻¹ := fun p hp ↦
    (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res (𝟙 Z) y (le p) hp _).trans
      ((gm_pull (𝟙 Z) r y _ (le p hp) _).trans (by rw [Category.id_comp]))))
  have hM := gm_pull_g M r (𝟙 Z) y p.1 q.1 hy.1.1 hy.2.1
  have hL := gm_pull_g L r (𝟙 Z) y p.2 q.2 hy.1.2 hy.2.2
  rw [Category.id_comp] at hM hL
  have hd := gm_div (L.pull r) (M.pull r) (𝟙 Z) y p q hy
  have k := isoOn_gm hw r y (hr y) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2.2) (mem_pull.1 hy.1.1) (mem_pull.1 hy.2.1)
  refine (gm_res (𝟙 Z) y inf_le_left hy _).trans ((val p hy.1).trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans ?_
  refine (congrArg₂ (· * ·) (hd.trans (congrArg₂ (fun u v ↦ u * v⁻¹) hM hL))
    ((gm_res (𝟙 Z) y inf_le_right hy _).trans (val q hy.2))).trans ?_
  rw [eq_mul_inv_of_mul_eq k]
  simp only [mul_inv_rev, inv_inv]
  ac_rfl

end GlobalTheory.PicGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormResidueSignMul
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory

theorem KSp.sgn_mul_of_isQuad : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (s t : Fˣ), sgn E (s * t) = sgn E s * sgn E t := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE s t
  set H := (Units.map (Algebra.norm F : E →* F)).range with hH
  unfold sgn
  rw [← hH]
  by_cases hs : s ∈ H <;> by_cases ht : t ∈ H
  · simp [hs, ht, H.mul_mem hs ht]
  · have : s * t ∉ H := fun h => ht ((H.mul_mem_cancel_left hs).mp h)
    simp [hs, ht, this]
  · have : s * t ∉ H := fun h => hs ((H.mul_mem_cancel_right ht).mp h)
    simp [hs, ht, this]
  · have : s * t ∈ H := GlobalTheory.T.mul_mem_range_norm_of_not_mem F E c δ hE s t hs ht
    simp [hs, ht, this]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderIffPlacewise
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.HatPlace

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_integral : IsOpen {y : Af E | ∀ w, Valued.v (y w) ≤ 1} :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (A := fun v => v.adicCompletionIntegers E) fun _ => Valued.isOpen_valuationSubring _

theorem exists_approx {S : Set (Af E)} {z : Af E} (hz : z ∈ closure S) {n : OF E} (hn : n ≠ 0) :
    ∃ x ∈ S, ∃ y : Af E, (∀ w, Valued.v (y w) ≤ 1) ∧ z = x + iota n * y := by
  have hn0 : algebraMap (OF E) E n ≠ 0 := fun h => hn (Subtype.ext (Subtype.ext h))
  have ho : IsOpen ((fun t : Af E => algebraMap E (Af E) (algebraMap (OF E) E n)⁻¹ * (z - t)) ⁻¹'
      {y : Af E | ∀ w, Valued.v (y w) ≤ 1}) :=
    isOpen_integral.preimage (continuous_const.mul (continuous_const.sub continuous_id))
  obtain ⟨x, hx, hxS⟩ := mem_closure_iff.1 hz _ ho (fun w => by
    simp only [sub_self, mul_zero, zero_coord, map_zero, zero_le'])
  refine ⟨x, hxS, _, hx, ?_⟩
  rw [iota, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, one_mul, add_sub_cancel]

theorem mem_iff_val {J : Ideal (𝓞 E)} (hJ : J ≠ ⊥) (b : 𝓞 E) :
    b ∈ J ↔ ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (algebraMap E (Af E) (algebraMap (𝓞 E) E b) w) ≤
      WithZero.exp (-(multiplicity w.asIdeal J : ℤ)) := by
  conv_lhs => rw [← Ideal.iInf_maxPowDividing_eq hJ, Ideal.mem_iInf]
  refine forall_congr' fun P => ?_
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hJ, ← P.intValuation_le_pow_iff_mem,
    ← HeightOneSpectrum.valuation_of_algebraMap (K := E),
    ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← FiniteAdeleRing.algebraMap_apply]

theorem val_mul_le {c : Ideal (OF E)} (hc : c ≠ ⊥) {n : OF E} (hn : n ∈ c) {y : Af E} (hy : ∀ w, Valued.v (y w) ≤ 1)
    (w : HeightOneSpectrum (𝓞 E)) : Valued.v ((iota n * y) w) ≤
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)) := by
  rw [mul_coord, map_mul]
  exact (mul_le_mul' ((mem_iff_val (Ideal.map_ne_bot_of_ne_bot hc) _).1 (Ideal.mem_map_of_mem _ hn) w)
    (hy w)).trans_eq (mul_one _)

theorem mem_hatO_of_val {c : Ideal (OF E)} (hc : c ≠ ⊥) {z : Af E} (hz : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (z w) ≤
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))) : z ∈ hatO c := by
  have hN : 0 < Ideal.absNorm c := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨x, y, hy, hxy⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E _ hN).2 z
    (fun P => (hz P).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega))
  have hny : Ideal.absNorm c • y = iota ((Ideal.absNorm c : ℕ) : OF E) * y := by
    rw [nsmul_eq_mul, iota, map_natCast, map_natCast]
  rw [hny] at hxy
  have hx : x ∈ Ideal.map (algebraMap (OF E) (𝓞 E)) c := by
    rw [mem_iff_val (Ideal.map_ne_bot_of_ne_bot hc)]
    intro P
    have h1 : algebraMap E (Af E) (algebraMap (𝓞 E) E x) = z - iota ((Ideal.absNorm c : ℕ) : OF E) * y := by
      rw [hxy, add_sub_cancel_right]
    rw [h1, sub_coord]
    exact Valuation.map_sub_le _ (hz P) (val_mul_le hc (Ideal.absNorm_mem c) hy P)
  rw [hxy]
  exact add_mem (algebraMap_mem_hatO (mem_orderC.2 ⟨0, _, hx, by rw [map_zero, zero_add]⟩))
    (PicFin.mul_mem_hatO (Ideal.absNorm_mem c) hy)

theorem exists_integer {f : E} (hf : f ∈ maximalRealSubfield E)
    (h : ∀ w, Valued.v (algebraMap E (Af E) f w) ≤ 1) : ∃ a : OF E, algebraMap (OF E) E a = f := by
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E f fun w => by
    have := h w
    rwa [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  have h1 : IsIntegral ℤ f := hb ▸ b.isIntegral_coe
  have h2 : IsIntegral ℤ (⟨f, hf⟩ : maximalRealSubfield E) :=
    (isIntegral_algebraMap_iff (A := maximalRealSubfield E) (B := E) ).1 h1
  exact ⟨⟨_, h2⟩, rfl⟩

theorem mem_hatO_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ z : Af E,
    z ∈ hatO c ↔ ∃ a ∈ hatF (E := E), (∀ w, Valued.v (a w) ≤ 1) ∧ ∀ (w : HeightOneSpectrum (𝓞 E)),
      Valued.v (z w - a w) ≤
        WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)) := by
  intro E _ _ _ c hc z
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  constructor
  · intro hz
    obtain ⟨_, ⟨x, hx, rfl⟩, y, hy, rfl⟩ := exists_approx hz hn0
    obtain ⟨a, b, hb, rfl⟩ := mem_orderC.1 hx
    refine ⟨iota a, Subring.le_topologicalClosure _ ⟨_, (a : maximalRealSubfield E).2, rfl⟩,
      fun w => val_iota_le_one w a, fun w => ?_⟩
    rw [← sub_coord, map_add (f := _), add_assoc]
    erw [add_sub_cancel_left]
    rw [add_coord]
    exact Valuation.map_add_le _ ((mem_iff_val (Ideal.map_ne_bot_of_ne_bot hc) _).1 hb w) (val_mul_le hc hn hy w)
  · rintro ⟨a, ha, hai, hz⟩
    obtain ⟨_, ⟨f, hf, rfl⟩, y, hy, rfl⟩ := exists_approx ha hn0
    obtain ⟨a, rfl⟩ := exists_integer hf fun w => by
      have h1 : Valued.v ((iota n * y) w) ≤ 1 := by
        rw [mul_coord, map_mul]; exact mul_le_one' (val_iota_le_one w n) (hy w)
      have h2 := Valuation.map_sub_le _ (hai w) h1
      rwa [add_coord, add_sub_cancel_right] at h2
    have h1 : z - (algebraMap E (Af E) (algebraMap (OF E) E a) + iota n * y) ∈ hatO c := mem_hatO_of_val hc hz
    have h2 := add_mem h1 (add_mem (algebraMap_mem_hatO (algebraMap_mem_orderC c a)) (PicFin.mul_mem_hatO hn hy))
    exact sub_add_cancel z _ ▸ h2

end GlobalTheory.CMVal.HatPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEigSp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.UPel.HT.LieType

def eigSp {F : Type} [Field F] [NumberField F] {g : ℕ} (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (τ : F →+* ℂ) :
    Submodule ℂ (Fin g → ℂ) where
  carrier := {u | ∀ c : 𝓞 F, φ c *ᵥ u = τ (c : F) • u}
  add_mem' := by
    intro u v hu hv c
    rw [Matrix.mulVec_add, hu c, hv c, smul_add]
  zero_mem' := by intro c; simp
  smul_mem' := by
    intro a u hu c
    rw [Matrix.mulVec_smul, hu c, smul_comm]

theorem mem_eigSp {F : Type} [Field F] [NumberField F] {g : ℕ} (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (τ : F →+* ℂ)
    (u : Fin g → ℂ) : u ∈ eigSp φ τ ↔ ∀ c : 𝓞 F, φ c *ᵥ u = τ (c : F) • u := Iff.rfl

end GlobalTheory.UPel.HT.LieType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemExpSolCons
section
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCF

def solStep (c : ℂ) (V : Submodule ℂ (ℝ → ℂ)) : Submodule ℂ (ℝ → ℂ) :=
    { carrier := {f | Differentiable ℝ f ∧ (deriv f - c • f) ∈ V}
      add_mem' := fun {f g} hf hg => by
        refine ⟨hf.1.add hg.1, ?_⟩
        have e : deriv (f + g) - c • (f + g) = (deriv f - c • f) + (deriv g - c • g) := by
          funext x
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          rw [deriv_add (hf.1 x) (hg.1 x)]; ring
        rw [e]; exact add_mem hf.2 hg.2
      zero_mem' := ⟨differentiable_const 0, by
        have e : deriv (0 : ℝ → ℂ) - c • (0 : ℝ → ℂ) = 0 := by
          funext x; simp
        rw [e]; exact zero_mem _⟩
      smul_mem' := fun k f hf => by
        refine ⟨hf.1.const_smul k, ?_⟩
        have e : deriv (k • f) - c • (k • f) = k • (deriv f - c • f) := by
          funext x
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          rw [deriv_const_smul k (hf.1 x)]; simp only [smul_eq_mul]; ring
        rw [e]; exact Submodule.smul_mem _ _ hf.2 }

def expSol (l : List ℂ) : Submodule ℂ (ℝ → ℂ) := l.foldr solStep ⊥

theorem mem_expSol_nil {f : ℝ → ℂ} : f ∈ expSol [] ↔ f = 0 := Submodule.mem_bot ℂ

theorem mem_expSol_cons {c : ℂ} {l : List ℂ} {f : ℝ → ℂ} :
    f ∈ expSol (c :: l) ↔ Differentiable ℝ f ∧ (deriv f - c • f) ∈ expSol l := Iff.rfl

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

def expCurve (t : ℝ) : GA E a :=
  Matrix.GeneralLinearGroup.scalar (Fin a) (infId E (expU (t • (1 : Cinf E))))

abbrev scalD : Module.End ℂ (Sm E a) := lie E a (Central.scL a 1)

variable {E a}

theorem expCurve_add (s t : ℝ) : expCurve E a (s + t) = expCurve E a s * expCurve E a t := by
  unfold expCurve
  rw [add_smul, expU_add, map_mul, map_mul]

theorem expCurve_zero : expCurve E a 0 = 1 := by
  unfold expCurve
  rw [zero_smul, expU_zero, map_one, map_one]

end GlobalTheory.HCF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemInterConjIff
section
namespace GlobalTheory.ConjugateIntersectionMembership

theorem mem_inter_conj_iff {H : Type} [Group H] {T L : Subgroup H} {x g : H} :
    g ∈ GlobalTheory.LKLoc.locPart T L x ↔ g ∈ T ∧ x⁻¹ * g * x ∈ L := by
  rw [GlobalTheory.LKLoc.locPart, Subgroup.mem_inf, Subgroup.mem_map]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨x⁻¹ * g * x, h, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · simp [MulAut.conj_apply, mul_assoc]

end GlobalTheory.ConjugateIntersectionMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackBasisThetaEqF0Form
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

namespace GlobalTheory.BaseVacuum

theorem pullback_basis_theta_eq_F0 : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)), StandardLatticesGL3.pullB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') (GL3Theta.th0 (TaylorLogMetric.lamOf D cc δ) (B.ω₀ / 2)) z = F0 B.L B.ω₀ (Ix D n n') (phi B n n' z) := by
  intro D cc δ B n n' z
  have hth : GL3Theta.th0 (TaylorLogMetric.lamOf D cc δ) (B.ω₀ / 2) = Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2) := by
    exact (GlobalTheory.Mem.Col2.JetAlgebraic.thetaZero_periodLattice_eq B _).symm
  simp only [StandardLatticesGL3.pullB, F0, prodFn, hth, _root_.GlobalTheory.BaseVacuum.coordB_bas_eq_phi]
  exact Fintype.prod_equiv (ixE D n n') _ _ (fun _ => rfl)

end GlobalTheory.BaseVacuum
end

