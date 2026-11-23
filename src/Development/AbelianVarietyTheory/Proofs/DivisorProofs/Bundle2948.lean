module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantFieldConstCoeffs
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackOfIdempotentImagesAndActionPullbac
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.UPel.HT

theorem siegPB_of_zRel_actPB : ∀ (h h' M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (e : O)
    (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O)
    (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp B)
    (s₂ : S₂ ⟶ Sp B) (y : S₂ ⟶ S₁) (c₁ : SiegPre h M ζ s₁) (w₁ : SiegPre h' M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A))
    (c₂ : SiegPre h M ζ s₂) (w₂ : SiegPre h' M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)),
    ActPB w₂ act₂ w₁ act₁ y → ZRel e jl o κ c₁ w₁ act₁ → ZRel e jl o κ c₂ w₂ act₂ → SiegPB c₂ c₁ y := by
  intro h h' M B _ ζ O _ e jl n o κ S₁ S₂ s₁ s₂ y c₁ w₁ act₁ c₂ w₂ act₂ hA hZ₁ hZ₂
  obtain ⟨ψ, ψ₂, hψ, sψ, lψ, vψ, aψ⟩ := hA
  obtain ⟨inc₁, pr₁, mi₁, mp₁, ip₁, pi₁, L₁, V₁, -⟩ := hZ₁
  obtain ⟨inc₂, pr₂, mi₂, mp₂, ip₂, pi₂, L₂, V₂, -⟩ := hZ₂
  have ip₁' : inc₁.left ≫ pr₁.left = 𝟙 _ := by rw [← Over.comp_left, ip₁]; rfl
  have ip₂' : inc₂.left ≫ pr₂.left = 𝟙 _ := by rw [← Over.comp_left, ip₂]; rfl
  have pi₁' : pr₁.left ≫ inc₁.left = (act₁ e).left := by rw [← Over.comp_left, pi₁]
  have pi₂' : pr₂.left ≫ inc₂.left = (act₂ e).left := by rw [← Over.comp_left, pi₂]
  have K0 : inc₂.left ≫ (act₂ e).left = inc₂.left := by
    rw [← pi₂', ← Category.assoc, ip₂', Category.id_comp]
  obtain ⟨φ, hφ⟩ : ∃ φ : c₂.A.left ⟶ c₁.A.left, φ = inc₂.left ≫ ψ ≫ pr₁.left := ⟨_, rfl⟩
  have K1 : φ ≫ inc₁.left = inc₂.left ≫ ψ := by
    rw [hφ, Category.assoc, Category.assoc, pi₁', ← aψ e, ← Category.assoc, K0]
  have K2 : pr₂.left ≫ φ = ψ ≫ pr₁.left := by
    have : (act₁ e).left ≫ pr₁.left = pr₁.left := by
      rw [← pi₁', Category.assoc, ip₁', Category.comp_id]
    rw [hφ, ← Category.assoc, ← Category.assoc, pi₂', aψ e, Category.assoc, this]
  have hw : φ ≫ c₁.A.hom = c₂.A.hom ≫ y := by
    rw [hφ, Category.assoc, Category.assoc, Over.w pr₁, hψ.1.w, ← Category.assoc, Over.w inc₂]
  have hpb : IsPullback φ c₂.A.hom c₁.A.hom y := by
    let lft : ∀ s : PullbackCone c₁.A.hom y, s.pt ⟶ c₂.A.left := fun s =>
      hψ.1.lift (s.fst ≫ inc₁.left) s.snd (by rw [Category.assoc, Over.w inc₁]; exact s.condition) ≫ pr₂.left
    refine IsPullback.of_isLimit (c := PullbackCone.mk φ c₂.A.hom hw)
      (PullbackCone.IsLimit.mk hw lft (fun s => ?_) (fun s => ?_) (fun s m hm1 hm2 => ?_))
    · simp only [lft]
      rw [Category.assoc, K2, ← Category.assoc, hψ.1.lift_fst, Category.assoc, ip₁', Category.comp_id]
    · simp only [lft]
      rw [Category.assoc, Over.w pr₂, hψ.1.lift_snd]
    · have e₁ : m ≫ inc₂.left = hψ.1.lift (s.fst ≫ inc₁.left) s.snd
          (by rw [Category.assoc, Over.w inc₁]; exact s.condition) := by
        apply hψ.1.hom_ext
        · rw [hψ.1.lift_fst, Category.assoc, ← K1, ← Category.assoc, hm1]
        · rw [hψ.1.lift_snd, Category.assoc, Over.w inc₂, hm2]
      calc m = m ≫ inc₂.left ≫ pr₂.left := by rw [ip₂', Category.comp_id]
        _ = lft s := by rw [← Category.assoc, e₁]
  have hmul : ∀ (T : Over S₂) (x x' : T ⟶ c₂.A) (x₀ x₀' : Over.mk (T.hom ≫ y) ⟶ c₁.A),
      x₀.left = x.left ≫ φ → x₀'.left = x'.left ≫ φ → (x₀ * x₀').left = (x * x').left ≫ φ := by
    intro T x x' x₀ x₀' hx hx'
    haveI := mi₂
    haveI := mp₁
    have wx : ∀ z : T ⟶ c₂.A, ((z ≫ inc₂).left ≫ ψ) ≫ w₁.A.hom = (Over.mk (T.hom ≫ y)).hom := fun z => by
      rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w (z ≫ inc₂)]; rfl
    let X₀ : Over.mk (T.hom ≫ y) ⟶ w₁.A := Over.homMk ((x ≫ inc₂).left ≫ ψ) (wx x)
    let X₀' : Over.mk (T.hom ≫ y) ⟶ w₁.A := Over.homMk ((x' ≫ inc₂).left ≫ ψ) (wx x')
    have m := hψ.2 T (x ≫ inc₂) (x' ≫ inc₂) X₀ X₀' rfl rfl
    rw [← mul_comp] at m
    have e₀ : X₀ ≫ pr₁ = x₀ := by
      ext1
      rw [Over.comp_left, hx, hφ]
      show ((x ≫ inc₂).left ≫ ψ) ≫ pr₁.left = _
      rw [Over.comp_left]; simp only [Category.assoc]
    have e₀' : X₀' ≫ pr₁ = x₀' := by
      ext1
      rw [Over.comp_left, hx', hφ]
      show ((x' ≫ inc₂).left ≫ ψ) ≫ pr₁.left = _
      rw [Over.comp_left]; simp only [Category.assoc]
    rw [← e₀, ← e₀', ← mul_comp, Over.comp_left, m, hφ, Over.comp_left, Category.assoc, Category.assoc]
  have sq := ActUnr.sqMap_fst hw
  have sq' := ActUnr.sqMap_snd hw
  refine ⟨φ, ActUnr.sqMap hw, ⟨hpb, hmul⟩, ⟨sq, sq'⟩, ?_, fun a => ?_⟩
  · have f₁ : (inc₁ ⊗ₘ inc₁).left ≫ (fst w₁.A w₁.A).left = (fst c₁.A c₁.A).left ≫ inc₁.left := by
      rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
    have g₁ : (inc₁ ⊗ₘ inc₁).left ≫ (snd w₁.A w₁.A).left = (snd c₁.A c₁.A).left ≫ inc₁.left := by
      rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
    have f₂ : (inc₂ ⊗ₘ inc₂).left ≫ (fst w₂.A w₂.A).left = (fst c₂.A c₂.A).left ≫ inc₂.left := by
      rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
    have g₂ : (inc₂ ⊗ₘ inc₂).left ≫ (snd w₂.A w₂.A).left = (snd c₂.A c₂.A).left ≫ inc₂.left := by
      rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
    have E : (inc₂ ⊗ₘ inc₂).left ≫ ψ₂ = ActUnr.sqMap hw ≫ (inc₁ ⊗ₘ inc₁).left := by
      apply ActUnr.left_hom_ext
      · rw [Category.assoc, sψ.1, ← Category.assoc, f₂]
        simp only [Category.assoc]
        rw [f₁]
        rw [← Category.assoc (ActUnr.sqMap hw), sq, Category.assoc, K1]
      · rw [Category.assoc, sψ.2, ← Category.assoc, g₂]
        simp only [Category.assoc]
        rw [g₁]
        rw [← Category.assoc (ActUnr.sqMap hw), sq', Category.assoc, K1]
    have l₂ := GlobalTheory.TChart.AbLevel.lbIso_comp w₁.isLB w₂.isLB c₂.isLB lψ L₂
    have hN := pull_isLB c₁.isLB (ActUnr.sqMap hw)
    have l₁ := GlobalTheory.TChart.AbLevel.lbIso_comp w₁.isLB c₁.isLB hN L₁ ((GlobalTheory.CechPic.cls_eq_iff hN hN).1 rfl)
    rw [E] at l₂
    exact LBIso.trans c₂.isLB (pull_isLB w₁.isLB _) hN l₂ (LBIso.symm l₁)
  · calc (c₂.lev a).left ≫ φ = (c₂.lev a ≫ inc₂).left ≫ ψ ≫ pr₁.left := by
          rw [hφ, Over.comp_left, Category.assoc]
      _ = (w₂.lev (jl a)).left ≫ ψ ≫ pr₁.left := by rw [V₂ a]
      _ = y ≫ (w₁.lev (jl a)).left ≫ pr₁.left := by rw [← Category.assoc, vψ, Category.assoc]
      _ = y ≫ (c₁.lev a).left := by rw [← V₁ a, Over.comp_left, Category.assoc, ip₁', Category.comp_id]

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SympAtPullbackIff
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.SympLevLocus

def SympAt {S : Scheme.{0}} {A : Over S} [GrpObj A] (P : LB (G2 A).left) (h M : ℕ)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) (k : Type) [Field k] (x : Sp k ⟶ S) (z : kˣ) : Prop :=
  (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M • b)) ∧
    (∀ g : Over.mk x ⟶ A, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g) ∧
    ∀ a b, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) M (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b)
      (unitOn (z ^ (2 * omegaStd a b)))

theorem isSympLev_iff {S : Scheme.{0}} {A : Over S} [GrpObj A] (P : LB (G2 A).left) (h M : ℕ) {B : Type}
    [CommRing B] (ζ : B) (t₁ : S ⟶ Sp B) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) :
    IsSympLev P h M ζ t₁ lev ↔ (∀ a b, lev (a + b) = lev a * lev b) ∧ (∀ a, lev a ^ M = 1) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k) (z : kˣ), x ≫ t₁ = spMap β →
        (z : k) = β ζ → SympAt P h M lev k x z :=
  Iff.rfl

end GlobalTheory.SympLevLocus

namespace GlobalTheory.SympLevLocus


open GlobalTheory.SiegelPull in
theorem sympAt_pullback_iff {S T : Scheme.{0}} (g : T ⟶ S) {A : Over S} [GrpObj A] [IsCommMonObj A] {A' : Over T}
    [GrpObj A'] [IsCommMonObj A'] {P : LB (G2 A).left} {P' : LB (G2 A').left} {φ : A'.left ⟶ A.left}
    {φ₂ : (G2 A').left ⟶ (G2 A).left} {h M : ℕ} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)}
    {lev' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ A')} (hP : P.IsLB) (hP' : P'.IsLB)
    (pb : IsGrpPullback A' A g φ) (sq : IsSquare φ φ₂) (iso : LBIso P' (P.pull φ₂))
    (hl : ∀ a, (lev' a).left ≫ φ = g ≫ (lev a).left) (k : Type) [Field k] (x : Sp k ⟶ T) (z : kˣ) :
    SympAt P' h M lev' k x z ↔ SympAt P h M lev k (x ≫ g) z := by
  have push : ∀ a, pushHom pb (Over.mk x) (toUnit (Over.mk x) ≫ lev' a) = toUnit (Over.mk (x ≫ g)) ≫ lev a := by
    intro a
    apply Over.OverMorphism.ext
    show ((toUnit (Over.mk x)).left ≫ (lev' a).left) ≫ φ = (toUnit (Over.mk (x ≫ g))).left ≫ (lev a).left
    rw [Category.assoc, hl, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
    rfl
  have inj := push_injective pb (Over.mk x)
  have surj := push_surjective pb (Over.mk x)
  refine and_congr (forall_congr' fun a => ?_) (and_congr ⟨fun H g₀ hg₀ => ?_, fun H g₀ hg₀ => ?_⟩
    (forall_congr' fun a => forall_congr' fun b => ?_))
  · rw [← inj.eq_iff, push, map_one]
  · obtain ⟨g₁, rfl⟩ := surj g₀
    obtain ⟨a, ha⟩ := H g₁ (inj (by rw [map_pow, map_one]; exact hg₀))
    exact ⟨a, (push a).symm.trans (congrArg _ ha)⟩
  · obtain ⟨a, ha⟩ := H (pushHom pb (Over.mk x) g₀) (by rw [← map_pow, hg₀, map_one])
    exact ⟨a, inj ((push a).trans ha)⟩
  · exact weilIs_grpPullback_of_comm S T A A' g φ _ _ (pull_isLB hP _) (pull_isLB hP' _) pb
      (diag_iso sq iso) (Over.mk x) M _ _ _ _ _
      (congrArg (fun q => q.left) (push a).symm) (congrArg (fun q => q.left) (push b).symm)

end GlobalTheory.SympLevLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTranslateCoefficientsZero
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.VertSpanZero

theorem snd_valR_mul_prod : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (S : Type) [CommRing S] (g : Sp S ⟶ G.left) (g' : tEpsG (g ≫ G.hom) ⟶ G), g'.left = spMap (algebraMap S (DualNumber S)) ≫ g → ∀ (n : ℕ) (u : Fin n → (tEpsG (g ≫ G.hom) ⟶ G)), (∀ a, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (u a).left = (1 : Over.mk (g ≫ G.hom) ⟶ G).left) → ∀ (O : G.left.Opens), ⊤ ≤ g ⁻¹ᵁ O → ∀ f : Γ(G.left, O), (valR (g' * (List.ofFn u).prod).left O f).snd = ∑ a, (valR (g' * u a).left O f).snd := _root_.GlobalTheory.EpsAdd.snd_valR_mul_prod

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

theorem isCombAtG_zero {S : Type} [CommRing S] (x : Sp S ⟶ X) {n : ℕ} (e : Fin n → (Sp (DualNumber S) ⟶ t.G.left))
    (he : ∀ i, IsTanAtG t x (e i)) : IsCombAtG t x e 0 (1 : tEpsG x ⟶ t.G).left := by
  refine ⟨fun _ => 1, fun i => ?_, ?_⟩
  · show (1 : tEpsG x ⟶ t.G).left = spMap (epsMul 0) ≫ e i
    rw [epsMul_zero', spMap_comp_eq, Category.assoc, (he i).2]
    let k : tEpsG x ⟶ Over.mk x := Over.homMk (spMap (algebraMap S (DualNumber S))) rfl
    exact congrArg CommaMorphism.left (MonObj.comp_one k).symm
  · simp

theorem isTanAtG_one {S : Type} [CommRing S] (x : Sp S ⟶ X) : IsTanAtG t x (1 : tEpsG x ⟶ t.G).left :=
  ⟨Over.w (1 : tEpsG x ⟶ t.G), congrArg CommaMorphism.left (MonObj.comp_one (redOver x))⟩

theorem isTanAtG_bc {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {x : Sp R ⟶ X}
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v) : IsTanAtG t (spMap φ ≫ x) (spMap (dualMap φ) ≫ v) := by
  have e1 : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp φ := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have e2 : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (dualMap φ) = φ.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  constructor
  · rw [Category.assoc, hv.1, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e1]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e2, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, hv.2]
    let k : Over.mk (spMap φ ≫ x) ⟶ Over.mk x := Over.homMk (spMap φ) rfl
    exact congrArg CommaMorphism.left (MonObj.comp_one k)

theorem coeffs_zero_at (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (hB : GlobalTheory.LineNorm.IsTanBasis t (chart U) v) {S : Type} [CommRing S] (y : Sp S ⟶ t.G.left)
    (φ : Γ(X, U.1) →+* S) (hy : y ≫ t.G.hom = spMap φ ≫ chart U) (wt : Fin n → (Sp (DualNumber S) ⟶ t.G.left))
    (hwt : ∀ a, IsTranslate t φ y (v a) (wt a)) (V : t.G.left.Opens) (hV : IsAffineOpen V) (hyV : ⊤ ≤ y ⁻¹ᵁ V)
    (d : Fin n → S) (hd : ∀ f : Γ(t.G.left, V), ∑ a, d a * (valR (wt a) V f).snd = 0) : d = 0 := by
  have hB2 := hB.2 S φ
  rw [← hy] at hB2
  have hT : ∀ i, IsTanAtG t (y ≫ t.G.hom) (spMap (dualMap φ) ≫ v i) := fun i => hy ▸ isTanAtG_bc t φ (hB.1 i)
  let g' : tEpsG (y ≫ t.G.hom) ⟶ t.G := Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ y) (Category.assoc _ _ _)
  have hwt' : ∀ a, ∃ g₁ v₁ : tEpsG (y ≫ t.G.hom) ⟶ t.G, g₁.left = spMap (algebraMap S (DualNumber S)) ≫ y ∧
      v₁.left = spMap (dualMap φ) ≫ v a ∧ (g₁ * v₁).left = wt a := hwt
  choose g₁ v₁ hg₁ hv₁ hw₁ using hwt'
  have hg₁' : ∀ a, g₁ a = g' := fun a => Over.OverMorphism.ext (hg₁ a)
  have ek : ∀ a, spMap (epsMul (d a)) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap S (DualNumber S)) :=
    fun a => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, epsMul_comp_algebraMap]
  let k : Fin n → (tEpsG (y ≫ t.G.hom) ⟶ tEpsG (y ≫ t.G.hom)) := fun a =>
    Over.homMk (spMap (epsMul (d a))) (by
      change _ ≫ spMap (algebraMap S (DualNumber S)) ≫ y ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y ≫ t.G.hom
      rw [← Category.assoc, ek])
  have hkg : ∀ a, k a ≫ g' = g' := fun a => Over.OverMorphism.ext (by
    change spMap (epsMul (d a)) ≫ spMap (algebraMap S (DualNumber S)) ≫ y = spMap (algebraMap S (DualNumber S)) ≫ y
    rw [← Category.assoc, ek])
  let u : Fin n → (tEpsG (y ≫ t.G.hom) ⟶ t.G) := fun a => k a ≫ v₁ a
  have hul : ∀ a, (u a).left = spMap (epsMul (d a)) ≫ spMap (dualMap φ) ≫ v a := fun a => by
    change spMap (epsMul (d a)) ≫ (v₁ a).left = _
    rw [hv₁ a]
  have hu : ∀ a, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (u a).left =
      (1 : Over.mk (y ≫ t.G.hom) ⟶ t.G).left := fun a => by
    rw [hul a, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fst_comp_epsMul]
    exact (hT a).2
  have hmul : ∀ a, (g' * u a).left = spMap (epsMul (d a)) ≫ wt a := fun a => by
    rw [← hw₁ a, hg₁' a]
    change (g' * (k a ≫ v₁ a)).left = (k a ≫ (g' * v₁ a)).left
    rw [MonObj.comp_mul, hkg a]
  have hwtV : ∀ a, ⊤ ≤ wt a ⁻¹ᵁ V := fun a =>
    GlobalTheory.CechKS.le_preimage_of_red (GlobalTheory.LogKSLin.translate_red (hB.1 a) hy (hwt a)) hyV
  have hred := red_mul_prod y g' rfl u hu
  have hTV := GlobalTheory.CechKS.le_preimage_of_red hred hyV
  have hg'V : ⊤ ≤ g'.left ⁻¹ᵁ V :=
    GlobalTheory.Points.le_preimage_comp (spMap (algebraMap S (DualNumber S))) y hyV (GlobalTheory.Points.le_preimage_top _)
  have hsnd : ∀ f, (valR (g' * (List.ofFn u).prod).left V f).snd = 0 := fun f => by
    rw [snd_valR_mul_prod _ t.G S y g' rfl n u hu V hyV f]
    simp_rw [hmul, fun a => snd_valR_epsMul (wt a) V (hwtV a) (d a) f]
    exact hd f
  have hval : ∀ f, valR (g' * (List.ofFn u).prod).left V f = valR g'.left V f := fun f => by
    have h1 := GlobalTheory.Points.valR_spMap_comp (TrivSqZeroExt.fstHom S S S).toRingHom _ V hTV f
    rw [hred] at h1
    have h2 : valR g'.left V f = algebraMap S (DualNumber S) (valR y V f) :=
      GlobalTheory.Points.valR_spMap_comp (algebraMap S (DualNumber S)) y V hyV f
    rw [h2]
    ext
    · simpa [TrivSqZeroExt.algebraMap_eq_inl] using h1.symm
    · simpa [TrivSqZeroExt.algebraMap_eq_inl] using hsnd f
  have hTeq := GlobalTheory.Points.ext_of_valR hV hTV hg'V hval
  have hP : (List.ofFn u).prod = 1 := mul_eq_left.mp (Over.OverMorphism.ext hTeq)
  have hc1 : IsCombAtG t (y ≫ t.G.hom) (fun i => spMap (dualMap φ) ≫ v i) d (1 : tEpsG (y ≫ t.G.hom) ⟶ t.G).left :=
    ⟨u, hul, by rw [hP]⟩
  exact (hB2 _ (isTanAtG_one t _)).unique hc1 (isCombAtG_zero t _ _ hT)

end GlobalTheory.VertSpanZero


open GlobalTheory.VertSpanZero in
theorem GlobalTheory.VertSpan.coeffs_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (S : Type) [CommRing S] (g₀ : Sp S ⟶ t.G.left) (W : t.G.left.Opens), W ≤ t.G.hom ⁻¹ᵁ U.1 → ⊤ ≤ g₀ ⁻¹ᵁ W → ∀ c : Fin n → S, (∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (φ' : Γ(X, U.1) →+* S') (wt : Fin n → (Sp (DualNumber S') ⟶ t.G.left)), (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ' ≫ chart U → (∀ a, IsTranslate t φ' (spMap ρ ≫ g₀) (v a) (wt a)) → ∀ (O : t.G.left.Opens), O ≤ W → ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(t.G.left, O), ∑ a, ρ (c a) * (valR (wt a) O f).snd = 0) → c = 0 := by
  intro E _ _ _ H X t U n v hv hb S _ g₀ W hWU hg₀ c hc
  have hB := GlobalTheory.LineNorm.isTanBasis_of_basis E H X t Γ(X, U.1) (chart U) n v hv hb
  have key : ∀ (J : Ideal S) (_ : J.IsMaximal) (a : Fin n), algebraMap S (Localization.AtPrime J) (c a) = 0 := by
    intro J _
    let ρ := algebraMap S (Localization.AtPrime J)
    have hyW : ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ W :=
      GlobalTheory.Points.le_preimage_comp (spMap ρ) g₀ hg₀ (GlobalTheory.Points.le_preimage_top _)
    obtain ⟨V, hVa, hzV, hVW⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp t.G.left.isBasis_affineOpens)
      (show (spMap ρ ≫ g₀).base (IsLocalRing.closedPoint (Localization.AtPrime J)) ∈ W from hyW trivial)
    have hyV := le_preimage_of_closedPoint (spMap ρ ≫ g₀) V hzV
    have hyU : ⊤ ≤ ((spMap ρ ≫ g₀) ≫ t.G.hom) ⁻¹ᵁ U.1 :=
      GlobalTheory.Points.le_preimage_comp _ t.G.hom (hVW.trans hWU) hyV
    let φ : Γ(X, U.1) →+* Localization.AtPrime J := (GlobalTheory.Points.valMap _ U.1 hyU).hom
    have hy : (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ ≫ chart U :=
      (GlobalTheory.Points.specMap_valMap_fromSpec U.2 _ hyU).symm
    have hex := fun a => (existsUnique_isTranslate t φ hy (hv a)).exists
    choose wt hwt using hex
    have := coeffs_zero_at t U v hB (spMap ρ ≫ g₀) φ hy wt hwt V hVa hyV (fun a => ρ (c a))
      (hc _ ρ φ wt hy hwt V hVW hyV)
    exact fun a => congrFun this a
  funext a
  exact eq_zero_of_localization (c a) fun J hJ => key J hJ a
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentKillingWeightZeroMapsToAbelianPartUnit
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HeatMod.TorField

open TrivSqZeroExt (inl inr)

theorem residue_eq_zero_of_sq {B : Type} [CommRing B] [IsLocalRing B] (x : B) (h : x * x = 0) :
    IsLocalRing.residue B x = 0 :=
  (IsLocalRing.residue_eq_zero_iff x).2 ((IsLocalRing.mem_maximalIdeal x).2 (mem_nonunits_iff.2 fun hu => by
    have := hu.mul hu
    rw [h] at this
    exact not_isUnit_zero this))

theorem lieExp_comp_q_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (u : Fin n → (epsR R ⟶ Y.H)), (∀ a, IsTangent (u a)) → (∀ a, (u a).left = (tv (v a)).left) → ∀ (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ e : Fin n → R, (∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0) → ∀ (B : Type) [CommRing B] [IsLocalRing B] (ψ : DualNumber R →+* B), spMap ψ ≫ (GlobalTheory.SqZero.lieExp u (fun a => (TrivSqZeroExt.inr (e a) : DualNumber R)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) ≫ Y.q).left = spMap ψ ≫ (1 : epsR R ⟶ Q.P.A).left := by
  intro R _ _ Q O _ _ _ oa Y n v u ht hu dd hd e hw B _ _ ψ
  letI : Algebra R B := (ψ.comp (TrivSqZeroExt.inlHom R R)).toAlgebra
  let ψ' : DualNumber R →ₐ[R] B := { ψ with commutes' := fun r => rfl }
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  let c : Fin n → DualNumber R := fun a => inr (e a)
  have hc : ∀ a, c a * c a = 0 := fun _ => TrivSqZeroExt.inr_mul_inr _ _ _
  let p : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (DualNumber R) ⟶ Y.H := GlobalTheory.SqZero.lieExp u c hc
  let z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ Y.H := 1
  let t : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ Y.H := ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ' ≫ p
  have hψ : (ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ').left = spMap ψ := ReciprocityTheory.ChartRestriction.G.Chart.spMap_left ψ'
  have e1 : spMap ψ ≫ (p ≫ Y.q).left = t.left ≫ Y.q.left := by
    rw [← hψ]; rfl
  have e2 : spMap ψ ≫ (1 : epsR R ⟶ Q.P.A).left = z.left ≫ Y.q.left := by
    rw [← hψ, ← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [ReciprocityTheory.ChartRestriction.G.Chart.comp_one', MonObj.one_comp]
  show spMap ψ ≫ (p ≫ Y.q).left = _
  rw [e1, e2]

  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.hom_ext_of_local (R := CommRingCat.of B) ?_ ?_
  · letI : Algebra R (IsLocalRing.ResidueField B) :=
      ((IsLocalRing.residue B).comp (algebraMap R B)).toAlgebra
    let r : B →ₐ[R] IsLocalRing.ResidueField B := { IsLocalRing.residue B with commutes' := fun _ => rfl }
    have htan : IsTangent p :=
      GlobalTheory.Reg.isTangent_of_isLieComb ht ((GlobalTheory.SqZero.isLieComb_iff_lieExp e p).2 rfl)
    have hrc : r.comp ψ' = (Algebra.ofId R (IsLocalRing.ResidueField B)).comp (ReciprocityTheory.ChartRestriction.G.Chart.fstD R) :=
      DualNumber.algHom_ext (by
        have : r (ψ' DualNumber.eps) = 0 := residue_eq_zero_of_sq _ (by
          rw [← map_mul, DualNumber.eps_mul_eps, map_zero])
        rw [AlgHom.comp_apply, this, AlgHom.comp_apply]
        simp [ReciprocityTheory.ChartRestriction.G.Chart.fstD])
    have hr : ReciprocityTheory.ChartRestriction.G.Chart.spMap r ≫ t = ReciprocityTheory.ChartRestriction.G.Chart.spMap r ≫ z := by
      rw [ReciprocityTheory.ChartRestriction.G.Chart.comp_one']
      show ReciprocityTheory.ChartRestriction.G.Chart.spMap r ≫ ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ' ≫ p = 1
      rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hrc, ← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp,
        Category.assoc, show ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD R) ≫ p = 1 from
          (ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff p).2 htan, ReciprocityTheory.ChartRestriction.G.Chart.comp_one']
    have H : (ReciprocityTheory.ChartRestriction.G.Chart.spMap r).left ≫ t.left ≫ Y.q.left =
        (ReciprocityTheory.ChartRestriction.G.Chart.spMap r).left ≫ z.left ≫ Y.q.left := by
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (fun f => Over.Hom.left f ≫ Y.q.left) hr
    rw [ReciprocityTheory.ChartRestriction.G.Chart.spMap_left] at H
    have hcp : (Spec.map (CommRingCat.ofHom r.toRingHom)).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField B)) =
        IsLocalRing.closedPoint (CommRingCat.of B) := IsLocalRing.comap_closedPoint (IsLocalRing.residue B)
    rw [← hcp]
    exact congrArg (fun f => f (IsLocalRing.closedPoint (IsLocalRing.ResidueField B))) H
  · intro U h₁ h₂
    have H : ∀ g, valR (t.left ≫ Y.q.left) U g = valR (z.left ≫ Y.q.left) U g := by
      intro g
      have hz : ⊤ ≤ z.left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ U) := h₂
      let e' : Fin n → B := fun a => ψ' (c a)
      have he' : ∀ i j, e' i * e' j = 0 := fun i j => by
        simp only [e', ← map_mul, c, TrivSqZeroExt.inr_mul_inr, map_zero]
      obtain ⟨b₁, b₂⟩ := valR_prod hu ht hd e' he' z (Y.q.left ⁻¹ᵁ U) hz Finset.univ
      have ht' : t = (∏ i ∈ Finset.univ, (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R (e' i) (he' i i)) ≫ u i :
          ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ Y.H)) * z := by
        rw [_root_.mul_one]
        exact GlobalTheory.SqZero.comp_lieExp u ψ' c hc
      rw [← ht'] at b₁ b₂
      have hF : pbT Y.q.left g (Y.q.left ⁻¹ᵁ U) = (Y.q.left.appLE U (Y.q.left ⁻¹ᵁ U) le_rfl).hom g :=
        GlobalTheory.KS.pbT_of_le _ le_rfl g
      have hwF := hw U _ (isWt_pbT Y U g (Y.q.left ⁻¹ᵁ U) le_rfl)
      rw [← GlobalTheory.Points.valR_appLE t.left Y.q.left le_rfl b₁ g, ← GlobalTheory.Points.valR_appLE z.left Y.q.left le_rfl hz g,
        ← hF, b₂]
      have hz' : z.left ≫ Y.H.hom = spMap (algebraMap R B) := Over.w z
      have key : ∀ i, e' i = ψ (inr 1) * algebraMap R B (e i) := fun i => by
        show ψ (inr (e i)) = ψ (inr 1) * ψ (inl (e i))
        rw [← map_mul]
        congr 1
        ext <;> simp
      have hv := congrArg (valR z.left (Y.q.left ⁻¹ᵁ U)) hwF
      set_option synthInstance.maxHeartbeats 100000 in
        rw [GlobalTheory.ZH.CrdCalc.valR_eq _ _ hz, map_sum, GlobalTheory.ZH.CrdCalc.valR_eq _ _ hz, map_zero] at hv
      simp only [← GlobalTheory.ZH.CrdCalc.valR_eq _ _ hz, WtAlg.valR_mul'' _ _ hz,
        GlobalTheory.Points.valR_constFn_of_over _ _ _ hz' _ hz] at hv
      simp only [key, _root_.mul_assoc, ← Finset.mul_sum, hv, mul_zero, add_zero]
    ext g
    have := H g
    rw [GlobalTheory.ZH.CrdCalc.valR_eq _ _ h₁, GlobalTheory.ZH.CrdCalc.valR_eq _ _ h₂] at this
    exact (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.injective this

end GlobalTheory.HeatMod.TorField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointFromFormalRaynaudPointSameDerivaStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_point_from_formal_raynaud_point_same_derivations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∀ (x' : Sp Ω ⟶ t.G.left) (hx' : x' ≫ t.G.hom = spMap φ), GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f) := by
  first | exact @GlobalTheory.Heat.FormalDer.main | exact GlobalTheory.Heat.FormalDer.main | (intros; apply GlobalTheory.Heat.FormalDer.main <;> assumption)
end

