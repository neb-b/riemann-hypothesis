module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TestObj
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.DenseGenericOfFlat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM
open GlobalTheory.SiegelRingChange GlobalTheory.SiegelPullComp

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g h k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

theorem dense_generic_of_flat [IsDomain o] (s : S ⟶ Sp o) [Flat s] : Dense {x : S | (s x).asIdeal = ⊥} := by
  intro x
  obtain ⟨y, hy⟩ := S.affineCover.covers x
  have hcomp : Flat (S.affineCover.f (S.affineCover.idx x) ≫ s) :=
    MorphismProperty.comp_mem _ _ _ inferInstance ‹Flat s›
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (S.affineCover.f (S.affineCover.idx x) ≫ s)
  have hfl : φ.hom.Flat := by
    rw [← HasRingHomProperty.Spec_iff (P := @Flat), hφ]
    exact hcomp
  have hsp : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum o) ⤳ PrimeSpectrum.comap φ.hom y :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal o) ≤ _ from bot_le)
  obtain ⟨y', hy'1, hy'2⟩ := RingHom.Flat.generalizingMap_comap hfl hsp
  have hφy := congrArg (fun m => (m y').asIdeal) hφ
  have hmem : S.affineCover.f (S.affineCover.idx x) y' ∈ {x : S | (s x).asIdeal = ⊥} := by
    change ((S.affineCover.f (S.affineCover.idx x) ≫ s) y').asIdeal = ⊥
    refine Eq.trans ?_ (congrArg PrimeSpectrum.asIdeal hy'2)
    exact hφy.symm
  have h₁ : S.affineCover.f (S.affineCover.idx x) y' ⤳ S.affineCover.f (S.affineCover.idx x) y :=
    hy'1.map (S.affineCover.f (S.affineCover.idx x)).continuous
  have h₂ : S.affineCover.f (S.affineCover.idx x) y ⤳ x := by rw [hy]
  exact (h₁.trans h₂).mem_closed isClosed_closure (subset_closure hmem)

theorem dense_generic_spMap {O : Type} [CommRing O] [IsDomain O] (β : o →+* O) (hβ : Function.Injective β) :
    Dense {x : Sp O | (spMap β x).asIdeal = ⊥} := by
  intro x
  have hη : (show ↥(Sp O) from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O)) ⤳ x :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal O) ≤ x.asIdeal from bot_le)
  refine hη.mem_closed isClosed_closure (subset_closure ?_)
  change (PrimeSpectrum.comap β ⟨⊥, Ideal.isPrime_bot⟩).asIdeal = ⊥
  exact Ideal.comap_bot_of_injective β hβ

namespace SFam
variable {ζ : o}

theorem hom_ext (F : SFam h k ζ) {s' : S ⟶ Sp o} (c : SiegPre h k ζ s') (f f' : S ⟶ F.X)
    (hs : f ≫ F.s = f' ≫ F.s) (h₁ : SiegPB c F.univ f) (h₂ : SiegPB c F.univ f') : f = f' := by
  apply hom_ext_of_fromSpecStalk
  intro x
  obtain ⟨c', hc'⟩ := (siegPre_pullback h k o ζ S (Spec (S.presheaf.stalk x)) s' (S.fromSpecStalk x ≫ s')
    (S.fromSpecStalk x) c rfl).1
  exact F.inj (S.presheaf.stalk x) _ _ _ c' (by simp only [Category.assoc, hs]) (pb_comp h₁ hc') (pb_comp h₂ hc')

theorem existsUnique (F : SFam h k ζ) {s' : S ⟶ Sp o} (c : SiegPre h k ζ s') (hr : IsReduced S)
    (hd : Dense {x : S | (s' x).asIdeal = ⊥}) (hc : c.Principal) :
    ∃! f : S ⟶ F.X, f ≫ F.s = s' ∧ SiegPB c F.univ f := by
  obtain ⟨f, hf, hpb⟩ := F.rep S s' c hr hd hc
  exact ⟨f, ⟨hf, hpb⟩, fun f' hf' => F.hom_ext c f' f (hf'.1.trans hf.symm) hf'.2 hpb⟩

theorem exists_point (F : SFam h k ζ) {O : Type} [CommRing O] [IsDomain O] (β : o →+* O) (hβ : Function.Injective β)
    (c : SiegPre h k ζ (spMap β)) (hc : c.Principal) : ∃ x : Sp O ⟶ F.X, x ≫ F.s = spMap β ∧ SiegPB c F.univ x := by
  obtain ⟨f, hf, hpb⟩ := F.rep (Sp O) (spMap β) c inferInstance (dense_generic_spMap β hβ) hc
  exact ⟨f, hf, hpb⟩

theorem nonempty (F : SFam h k ζ) {O : Type} [CommRing O] [IsDomain O] (β : o →+* O) (hβ : Function.Injective β)
    (c : SiegPre h k ζ (spMap β)) (hc : c.Principal) : Nonempty F.X := by
  obtain ⟨x, -, -⟩ := F.exists_point β hβ c hc
  exact ⟨x (show ↥(Sp O) from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O))⟩

theorem isReduced_and_dense [IsDomain o] (F : SFam h k ζ) : IsReduced F.X ∧ Dense {x : F.X | (F.s x).asIdeal = ⊥} := by
  have := F.smooth
  have : Smooth F.s := SmoothOfRelativeDimension.smooth (n := h * (h + 1) / 2) (f := F.s)
  have : IsReduced F.X := isReduced_of_smooth_of_isReduced F.s
  exact ⟨inferInstance, dense_generic_of_flat F.s⟩

theorem exists_iso [IsDomain o] (F F' : SFam h k ζ) :
    ∃ e : F.X ≅ F'.X, e.hom ≫ F'.s = F.s ∧ SiegPB F.univ F'.univ e.hom := by
  obtain ⟨hr, hd⟩ := F.isReduced_and_dense
  obtain ⟨hr', hd'⟩ := F'.isReduced_and_dense
  obtain ⟨f, hf, hpf⟩ := F'.rep F.X F.s F.univ hr hd F.princ
  obtain ⟨g, hg, hpg⟩ := F.rep F'.X F'.s F'.univ hr' hd' F'.princ
  have e₁ : f ≫ g = 𝟙 _ :=
    F.hom_ext F.univ _ _ (by rw [Category.assoc, hg, hf, Category.id_comp]) (pb_comp hpg hpf) (pb_id _)
  have e₂ : g ≫ f = 𝟙 _ :=
    F'.hom_ext F'.univ _ _ (by rw [Category.assoc, hf, hg, Category.id_comp]) (pb_comp hpf hpg) (pb_id _)
  exact ⟨⟨f, g, e₁, e₂⟩, hf, hpf⟩

theorem exists_baseChange (F : SFam h k ζ) {B : Type} [CommRing B] {ζ' : B} (j : o →+* B) (hi : Function.Injective j)
    (hj : j ζ = ζ') : ∃ (F' : SFam h k ζ') (π : F'.X ⟶ F.X),
      IsPullback π F'.s F.s (spMap j) ∧ SiegPB F'.univ F.univ π := by
  have sq := IsPullback.of_hasPullback F.s (spMap j)
  have hrc := siegPre_pull_ringChange h k o B ζ ζ' j F.X (pullback F.s (spMap j)) F.s
    (pullback.snd F.s (spMap j)) (pullback.fst F.s (spMap j)) hj pullback.condition
  obtain ⟨u, hu⟩ := hrc.1 F.univ
  refine ⟨SFam.mk (pullback F.s (spMap j)) (pullback.snd F.s (spMap j)) ?_
    (isQProjOver_of_isPullback_spMap j sq F.qproj) u (hrc.2.1 F.univ u hu F.princ) ?_ ?_,
    pullback.fst F.s (spMap j), sq, hu⟩
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := h * (h + 1) / 2)).of_isPullback sq F.smooth
  · intro T t c hr hd hc
    have hd' : Dense {x : T | ((t ≫ spMap j) x).asIdeal = ⊥} := by
      refine hd.mono fun x hx => ?_
      have hx' : (t x).asIdeal = ⊥ := hx
      change Ideal.comap j (t x).asIdeal = ⊥
      exact (congrArg (Ideal.comap j) hx').trans (Ideal.comap_bot_of_injective j hi)
    obtain ⟨f₀, hf₀, hpb⟩ := F.rep T (t ≫ spMap j) (down j hj c) hr hd' hc
    refine ⟨pullback.lift f₀ t hf₀, pullback.lift_snd _ _ _, ?_⟩
    have hpb' : SiegPB c F.univ (pullback.lift f₀ t hf₀ ≫ pullback.fst F.s (spMap j)) := by
      rw [pullback.lift_fst]
      exact hpb
    exact pb_cancel hu hpb'
  · intro R _ _ x y t c hxy hx hy
    refine pullback.hom_ext ?_ hxy
    have e : (x ≫ pullback.fst F.s (spMap j)) ≫ F.s = (y ≫ pullback.fst F.s (spMap j)) ≫ F.s := by
      simp only [Category.assoc, pullback.condition, reassoc_of% hxy]
    exact F.inj R _ _ (t ≫ spMap j) (down j hj c) e (pb_comp hu hx) (pb_comp hu hy)

theorem siegRep {p M : ℕ} (F : SFam h M (zetaZP p M))
    (sm : SmoothOfRelativeDimension (h * (h + 1) / 2) F.s) (qc : QuasiCompact F.s) (pr : F.univ.Principal) (pts unr) :
    GlobalTheory.Models.SiegRep (⟨F.X, F.s, sm, qc, F.univ, pr, pts, unr⟩ : SiegelFamily h p M) := by
  unfold GlobalTheory.Models.SiegRep
  refine ⟨F.qproj, fun T t c hr _ hfl hc => ?_⟩
  exact F.existsUnique c hr (dense_generic_of_flat t) hc

end SFam

theorem SFam.exists_sRep_siegRep {p M : ℕ} (hM : M ≠ 0) (F : SFam h M (zetaZP p M)) (Ag : SiegelFamily h p M)
    (H : SRep Ag) : ∃ Ag' : SiegelFamily h p M, SRep Ag' ∧ GlobalTheory.Models.SiegRep Ag' := by
  obtain ⟨hsep, hrep⟩ := H
  obtain ⟨hr, hd⟩ := F.isReduced_and_dense
  have := Ag.smooth
  have : Smooth Ag.s := SmoothOfRelativeDimension.smooth (n := h * (h + 1) / 2) (f := Ag.s)
  have : IsReduced Ag.X := isReduced_of_smooth_of_isReduced Ag.s
  obtain ⟨f, hf, hpf⟩ := hrep F.X F.s F.univ hr hd F.princ
  obtain ⟨g, hg, hpg⟩ := F.rep Ag.X Ag.s Ag.univ inferInstance (dense_generic_of_flat Ag.s) Ag.princ
  have hfg : f ≫ g = 𝟙 _ :=
    F.hom_ext F.univ _ _ (by rw [Category.assoc, hg, hf, Category.id_comp]) (pb_comp hpg hpf) (pb_id _)
  have : IsSeparated (g ≫ F.s) := by rw [hg]; exact hsep
  have : IsSeparated g := IsSeparated.of_comp g F.s
  have : IsClosedImmersion (f ≫ g) := by rw [hfg]; infer_instance
  have : IsClosedImmersion f := IsClosedImmersion.of_comp f g
  have := Ag.qc
  have qc : QuasiCompact F.s := by rw [← hf]; infer_instance
  refine ⟨⟨F.X, F.s, F.smooth, qc, F.univ, F.princ, ?_, ?_⟩, ?_, ?_⟩
  · intro C O _ _ _ _ _ _ _ _ hu hp β o ho ha
    obtain ⟨y, hy, hpy⟩ := Ag.points C O hu hp β o ho ha
    exact ⟨y ≫ g, by rw [Category.assoc, hg, hy], pb_comp hpg hpy⟩
  · intro K _ x o h₁ h₂
    have key : ∀ (s₁ : Sp (DualNumber K) ⟶ Sp (ZP p M)) (o₁ : SiegPre h M (zetaZP p M) s₁),
        s₁ = (x ≫ f) ≫ Ag.s → SiegPB o₁ Ag.univ (x ≫ f) → SiegPB o₁ Ag.univ (constPt (x ≫ f)) →
        x ≫ f = constPt (x ≫ f) := by
      rintro s₁ o₁ rfl
      exact Ag.unram K (x ≫ f) o₁
    have hc : constPt (x ≫ f) = constPt x ≫ f := by simp only [constPt, Category.assoc]
    have e : x ≫ f = constPt x ≫ f := by
      rw [← hc]
      refine key _ o (by rw [Category.assoc, hf]) (pb_comp hpf h₁) ?_
      rw [hc]
      exact pb_comp hpf h₂
    calc x = x ≫ (f ≫ g) := by rw [hfg, Category.comp_id]
      _ = (x ≫ f) ≫ g := (Category.assoc _ _ _).symm
      _ = (constPt x ≫ f) ≫ g := by rw [e]
      _ = constPt x := by rw [Category.assoc, hfg, Category.comp_id]
  · exact F.sRep F.smooth qc F.princ _ _
  · exact F.siegRep F.smooth qc F.princ _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end GlobalTheory.ZM
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsIsE8IsSharpBasis
section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.ZM.Model

section Away
variable {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ) {n : ℕ} (hn : n ≠ 0)

end Away

section Basis
variable (h : ℕ)

end Basis

section Use
open AlgebraicGeometry CategoryTheory MonObj
variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

end Use

section Zero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi Out.Inh
open scoped CategoryTheory.Obj
variable {o : Type} [CommRing o] {S : Scheme.{0}} {k : ℕ} {J : Type}

theorem corr_comm_pull {X X' Y : Scheme.{0}} (f : X ⟶ X') {K : Type} [Fintype K] (φ φ' : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb ((trivLB X').pull f) φ ε)) (b : LB.Gen (LB.LinComb ((trivLB X').pull f) φ' ε)) (h h' : Y ⟶ Y)
    (hh : h = 𝟙 Y) (hh' : h' = 𝟙 Y)
    (c : LB.Gen (LB.LinComb ((trivLB X').pull f) (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim)) (hc : ∀ j, c.s j = 1) :
    LB.Gen.Corr ((trivLB X').pull f) _ _ _ _ (LB.mulGen _ _ _ _ _ a (LB.pullGen _ _ _ b h))
      (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ b (LB.pullGen _ _ _ a h')) c) := by
  subst hh hh'
  intro j j'
  obtain rfl : j = fun _ _ => PUnit.unit := rfl
  obtain rfl : j' = fun _ _ => PUnit.unit := rfl
  intro _ _ _
  have e1 : ∀ (V W : Y.Opens) (h1 : V ≤ W) (U U' : Y.Opens) (h2 : W ≤ U) (h3 : W ≤ U') (u : Γ(Y, U)ˣ) (v : Γ(Y, U')ˣ),
      res h1 (res h2 u * res h3 v) = res (h1.trans h2) u * res (h1.trans h3) v := by
    intros; rw [map_mul, ZH.RealModel.res_res, ZH.RealModel.res_res]
  refine (e1 _ _ _ _ _ _ _ _ _).trans (Eq.trans ?_ (e1 _ _ _ _ _ _ _ _ _).symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (e1 _ _ _ _ _ _ _ _ _) ((congrArg _ (hc _)).trans (ZH.RealModel.res_one _))).symm
  rw [_root_.mul_one, _root_.mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact (ZH.RealModel.res_res _ _ _)
  · exact (ZH.RealModel.res_res _ _ _).symm

theorem isGen_one {X : Scheme.{0}} (L : LB X) (hL : ∀ i j, L.g i j = 1) : (⟨fun _ => 1⟩ : L.Gen).IsGen := by
  intro i j; rw [hL, _root_.one_mul]; exact (map_one _).trans (map_one _).symm

theorem weil_pull_zero {X : Scheme.{0}} (f : (𝟙_ (Over S)).left ⟶ X) (n : ℤ) {T : Over S} (x y : T ⟶ 𝟙_ (Over S)) :
    Out.WeilIs (𝟙_ (Over S)) ((trivLB X).pull f) n x y 1 := by
  intro p
  refine ⟨⊤, trivial, ⟨⟨_, _, isGen_one _ (linComb_g_one _ (linComb_triv_g _ _) _ _)⟩,
    ⟨_, _, isGen_one _ (linComb_g_one _ (linComb_triv_g _ _) _ _)⟩, rfl, rfl⟩, ?_⟩
  intro θx θy _ _
  have hc : Out.unitRes (T := T) ⊤ 1 = 1 := map_one _
  rw [hc]
  exact corr_comm_pull _ _ _ _ _ _ _ _ (ZH.RealModel.translT_id S _) (ZH.RealModel.translT_id S _) _
    (fun j => (congrArg _ (map_one _)).trans (ZH.RealModel.res_one _))

def zeroSieg (ζ : o) (s : S ⟶ Sp o) : SiegPre 0 k ζ s where
  A := 𝟙_ (Over S)
  ab := UU.isAbelianScheme_unit S
  P := trivLB _
  isLB := trivLB_isLB _
  rig₁ := ⟨_, ZH.RealModel.oneG_gen _ _⟩
  rig₂ := ⟨_, ZH.RealModel.oneG_gen _ _⟩
  symm := lbIso_of_g _ _ (fun _ _ => rfl) (linComb_triv_g _ _)
  lev := fun _ => 𝟙 _
  lev_add := fun _ _ => toUnit_unique _ _
  lev_tors := fun _ => toUnit_unique _ _
  geom := fun K _ _ x β z _ _ => ⟨fun a => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => toUnit_unique _ _⟩,
    fun g _ => ⟨0, toUnit_unique _ _⟩, fun a b => by
      have : unitOn (z ^ (2 * omegaStd a b)) = 1 := by simp [omegaStd, unitOn]
      rw [this]; exact weil_pull_zero _ _ _ _⟩

end Zero

end GlobalTheory.ZM.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Amp

variable {D : Datum H} {Xo : ∀ l : Level H, Moduli D l}

end Amp

section Refl

variable {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t₀ : SAB H U} {β : O →+* F}

end Refl

section Abelian

variable {O F : Type} [CommRing O] [Field F] (β : O →+* F) {X : Scheme.{0}} (s : X ⟶ Sp O) (t : SAB H X)

variable (A : Over X) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)

end Abelian

theorem flat_projSpace (R : Type) [CommRing R] (N : ℕ) : Flat (PSpace.str R N) :=
  haveI : IsZariskiLocalAtSource @Flat.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  IsZariskiLocalAtSource.of_openCover (P := @Flat) (ProjSpace.chartCover R N) fun (i : Fin (N + 1)) => by
    change Flat (ProjSpace.chartι R N i ≫ _)
    rw [ProjSpace.chartι_str, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (inferInstanceAs (Module.Flat R (MvPolynomial _ R)))

theorem isNormalScheme_projSpace (R : Type) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (N : ℕ) :
    Geo.Tor.IsNormalScheme (PSpace R N) := by
  refine (isNormalScheme_iff_pred _).1 (IsNormalScheme.of_forall_exists_isOpenImmersion fun x => ?_)
  obtain ⟨i, y, hy⟩ := (ProjSpace.chartCover R N).exists_eq x
  exact ⟨_, ProjSpace.chartι R N i, ProjSpace.isOpenImmersion_chartι R N i, IsNormalScheme.of_pred (ZJ.isNormalScheme_sp _), y, hy⟩

end GlobalTheory.Models

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotPelRepOfTwoPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

namespace DimZero
open Out.Inh GlobalTheory.ZM.Model

theorem translT_zero {T : Over S} (x : T ⟶ (zeroPolAV S).A) : (Out.translT (zeroPolAV S).A x).left = 𝟙 _ := by
  have : Out.translT (zeroPolAV S).A x = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [Out.translT]
    · exact toUnit_unique _ _
  rw [this]; rfl

theorem exists_gen {X : Scheme.{0}} (L : LB X) (hL : ∀ i j, L.g i j = 1) : ∃ t : L.Gen, t.IsGen ∧ ∀ i, t.s i = 1 :=
  ⟨⟨fun _ => 1⟩, fun i j => by
    rw [hL, _root_.one_mul]; exact (map_one _).trans (map_one _).symm, fun _ => rfl⟩

theorem corr_comm {X Y : Scheme.{0}} (L : LB X) [Unique L.ι] {K : Type} [Fintype K] (φ φ' : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb L φ ε)) (b : LB.Gen (LB.LinComb L φ' ε)) (h h' : Y ⟶ Y) (hh : h = 𝟙 Y) (hh' : h' = 𝟙 Y)
    (c : LB.Gen (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim)) (hc : ∀ j, c.s j = 1) :
    LB.Gen.Corr L _ _ _ _ (LB.mulGen _ _ _ _ _ a (LB.pullGen _ _ _ b h))
      (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ b (LB.pullGen _ _ _ a h')) c) := by
  subst hh hh'
  intro j j' _ _ _
  obtain rfl : j = fun _ => default := Subsingleton.elim _ _
  obtain rfl : j' = fun _ => default := Subsingleton.elim _ _
  have e1 : ∀ (V W : Y.Opens) (h1 : V ≤ W) (U U' : Y.Opens) (h2 : W ≤ U) (h3 : W ≤ U') (u : Γ(Y, U)ˣ) (v : Γ(Y, U')ˣ),
      res h1 (res h2 u * res h3 v) = res (h1.trans h2) u * res (h1.trans h3) v := by
    intros; rw [map_mul, DVR.res_res', DVR.res_res']
  refine (e1 _ _ _ _ _ _ _ _ _).trans (Eq.trans ?_ (e1 _ _ _ _ _ _ _ _ _).symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (e1 _ _ _ _ _ _ _ _ _) ((congrArg _ (hc _)).trans (map_one _))).symm
  rw [_root_.mul_one, _root_.mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact (DVR.res_res' _ _ _)
  · exact (DVR.res_res' _ _ _).symm

theorem weilIs_zero (L : LB (zeroPolAV S).A.left) [Unique L.ι] (hL : ∀ i j, L.g i j = 1) (n : ℤ) {T : Over S}
    (x y : T ⟶ (zeroPolAV S).A) : Out.WeilIs (zeroPolAV S).A L n x y 1 := by
  intro p
  have ex : ∀ z : Out.overRes (T := T) ⊤ ⟶ (zeroPolAV S).A, ∃ θ : Out.ThetaGrp _ L n _, θ.pt = z := fun z => by
    obtain ⟨t, ht, -⟩ := exists_gen (Out.thetaLB _ L n z) (linComb_g_one L hL _ _)
    exact ⟨⟨z, t, ht⟩, rfl⟩
  refine ⟨⊤, trivial, ?_, fun θx θy _ _ => ?_⟩
  · obtain ⟨θx, hx⟩ := ex (Out.overResι ⊤ ≫ x)
    obtain ⟨θy, hy⟩ := ex (Out.overResι ⊤ ≫ y)
    exact ⟨θx, θy, hx, hy⟩
  · have hc : Out.unitRes (T := T) ⊤ 1 = 1 := map_one _
    rw [hc]
    exact corr_comm L _ _ _ _ _ _ _ (translT_zero _) (translT_zero _) _
      (fun j => (congrArg _ (map_one _)).trans (map_one _))

def zeroSieg (k : ℕ) {B : Type} [CommRing B] (ζ : B) (s : S ⟶ Sp B) : SiegPre 0 k ζ s where
  A := (zeroPolAV S).A
  comm := (zeroPolAV S).isAb.comm
  ab := (zeroPolAV S).isAb
  P := trivLB _
  isLB := trivLB_isLB _
  rig₁ := (exists_gen _ (linComb_triv_g _ _)).imp fun _ h => h.1
  rig₂ := (exists_gen _ (linComb_triv_g _ _)).imp fun _ h => h.1
  symm := lbIso_of_g _ _ (fun _ _ => rfl) (linComb_triv_g _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => toUnit_unique _ _
  lev_tors := fun _ => toUnit_unique _ _
  geom := fun K _ _ x β z _ _ => by
    refine ⟨fun a => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => toUnit_unique _ _⟩,
      fun _ _ => ⟨0, toUnit_unique _ _⟩, fun a a' => ?_⟩
    have h1 : unitOn (z ^ (2 * omegaStd a a')) = 1 := by
      have : omegaStd a a' = 0 := by simp [omegaStd]
      rw [this, mul_zero, zpow_zero]
      exact map_one _
    rw [h1]
    exact @weilIs_zero S _ (inferInstanceAs (Unique (PUnit → PUnit))) (linComb_triv_g _ _) _ _ _ _

theorem principal_zeroSieg (k : ℕ) {B : Type} [CommRing B] (ζ : B) (s : S ⟶ Sp B) : (zeroSieg k ζ s).Principal := by
  refine ⟨?_, fun _ _ _ => toUnit_unique _ _⟩
  generalize hM : (zeroSieg k ζ s).diag = M
  have hg : ∀ i j, M.g i j = 1 := by subst hM; exact linComb_triv_g _ _
  have hU : ∃ i, M.U i = ⊤ := by
    subst hM; exact ⟨fun _ => PUnit.unit, top_unique fun y _ => Set.mem_iInter.2 fun _ => trivial⟩
  obtain ⟨i₀, hi₀⟩ := hU
  change LB (𝟙_ (Over S)).left at M
  change Out.RelAmple (𝟙_ (Over S)) M
  intro U hU
  haveI : IsIso (𝟙_ (Over S)).hom := by show IsIso (𝟙 S); infer_instance
  let Y := ((𝟙_ (Over S)).hom ⁻¹ᵁ U).toScheme
  have hp : ∀ i j, (Out.powOver (𝟙_ (Over S)) M U 1).g i j = 1 := fun i j => by
    exact linComb_g_one M hg _ _ i j
  let s0 : LB.Sec (Out.powOver (𝟙_ (Over S)) M U 1) :=
    ⟨fun _ => 1, by
      intro i j; rw [hp, Units.val_one, _root_.one_mul]; repeat erw [map_one]
      all_goals rfl⟩
  have hD : Out.nonzeroLocus s0 = ⊤ := by
    apply top_unique
    intro x _
    simp only [Out.nonzeroLocus, s0, Scheme.basicOpen_one]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i₀, Set.mem_iInter.2 fun _ => by
      show _ ∈ M.U i₀
      rw [hi₀]; trivial⟩
  refine ⟨1, le_rfl, 0, fun _ => s0, by simp only [iSup_const]; exact hD,
    fun _ => ⟨?_, fun _ => 1, ?_, ?_⟩⟩
  · rw [hD]
    have : IsAffine Y := hU
    exact isAffineOpen_top Y
  · intro j k
    erw [map_one]; (try erw [map_one]); (try erw [map_one]); exact (_root_.mul_one _).symm
  · intro p
    obtain ⟨a, rfl⟩ := surj_appLE ((𝟙_ (Over S)).hom ∣_ U) _ hD le_top p
    exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩

end DimZero

end GlobalTheory.ZM
end
end

