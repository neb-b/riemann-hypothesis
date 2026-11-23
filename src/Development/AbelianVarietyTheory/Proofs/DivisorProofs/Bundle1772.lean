module

public import Formalism.LocalToGlobal.Divisibility.RecBridgeNum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0725
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1353
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookLogSumSubSizeTermLeLowerBound
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

namespace GlobalTheory.LowMainTerm

theorem logHook_congr (n : ℕ) (a b : ℕ → ℝ) (h : ∀ i < n, a i = b i) :
    Formalism.BasicNotions.DV.logHook n a = Formalism.BasicNotions.DV.logHook n b := by
  unfold Formalism.BasicNotions.DV.logHook
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [h i (Finset.mem_range.mp hi)]
  · refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun l hl => ?_
    have hi' := Finset.mem_range.mp hi
    have hl' := (Finset.mem_Ioo.mp hl).2
    rw [h i hi', h l hl']

theorem pW_eq (D : D7) (j : Fin D.R.m) (ρ : D.what₂.Tau) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D j ρ = (D.R.sigW ((j : ℕ) + 1)).1 := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW
  rw [GlobalTheory.RecGaps.sig_Wc]

theorem sigW_fst (D : D7) (j : Fin D.R.m) : (D.R.sigW ((j : ℕ) + 1)).1 = D.R.k + (j : ℕ) := by
  simp [Formalism.BasicNotions.Ranks.sigW]

theorem hook_term (D : D7) (j : Fin D.R.m) (ρ : D.what₂.Tau) :
    Real.log ((GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D j ρ)
        (Formalism.IndefR.Links.aPl D j (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D j ρ) ρ) : ℕ) : ℝ)
      = Formalism.BasicNotions.DV.logHook (D.R.sigW ((j : ℕ) + 1)).1 (Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) ρ) := by
  have h1 : 1 ≤ (j : ℕ) + 1 := Nat.le_add_left 1 _
  have h2 : (j : ℕ) + 1 ≤ D.R.m := j.isLt
  rw [pW_eq, sigW_fst]
  have key : ∀ n < D.R.k + (j : ℕ),
      ((Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ n : ℕ) : ℝ) = Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) ρ n := by
    intro n hn
    have := GlobalTheory.RecordWeightVec.aPl_eq_aPlusQ D j ρ n hn
    unfold Formalism.BasicNotions.DV.aPlus
    rw [← this]
    push_cast
    rfl
  have rs := (GlobalTheory.BlockRows.rows_sizes D ((j : ℕ) + 1) h1 h2 ρ).1
  have hanti : ∀ (x y : ℕ), x ≤ y → y < D.R.k + (j : ℕ) →
      Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ y ≤ Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ x := by
    intro x y hxy hy
    have hx : x < D.R.k + (j : ℕ) := lt_of_le_of_lt hxy hy
    have e : (D.R.sigW ((j : ℕ) + 1)).1 = D.R.k + (j : ℕ) := sigW_fst D j
    have hy' : y < (D.R.sigW ((j : ℕ) + 1)).1 := e ▸ hy
    have hx' : x < (D.R.sigW ((j : ℕ) + 1)).1 := e ▸ hx
    have ha := rs.1 (show (⟨x, hx'⟩ : Fin _) ≤ ⟨y, hy'⟩ from hxy)
    have ex := rs.2.2 ⟨x, hx'⟩
    have ey := rs.2.2 ⟨y, hy'⟩
    have r : ((Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ y : ℕ) : ℝ)
        ≤ ((Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ x : ℕ) : ℝ) := by
      rw [key y hy, key x hx]
      simp only at ex ey
      rw [← ex, ← ey]
      exact_mod_cast ha
    exact_mod_cast r
  rw [(GlobalTheory.HookDiagram.hookOf_pos_log _ _ hanti).2]
  exact logHook_congr _ _ _ key

end GlobalTheory.LowMainTerm

namespace GlobalTheory.LowMainTerm

theorem sum_logHook_eq (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (j : Fin D.R.m) :
    (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ) = GlobalTheory.LiftLower.hookPlus D j := by
  have h1 : 1 ≤ (j : ℕ) + 1 := Nat.le_add_left 1 _
  have h2 : (j : ℕ) + 1 ≤ D.R.m := j.isLt
  have e1 : (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ)
      = ∑ z : Bool × G.HH D, Formalism.BasicNotions.DV.logHook (D.R.sigW ((j : ℕ) + 1)).1
          (Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) (tauPl D z)) :=
    Finset.sum_congr rfl fun z _ => Formalism.L2.DIV.NumTieH.logHook_eq D L Del h0 h1 h2 z
  rw [e1, Function.Bijective.sum_comp (tauPl_bijective D)
    (fun τ => Formalism.BasicNotions.DV.logHook (D.R.sigW ((j : ℕ) + 1)).1 (Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) τ))]
  unfold GlobalTheory.LiftLower.hookPlus
  exact (Finset.sum_congr rfl fun ρ _ => hook_term D j ρ).symm

theorem main_le_lowB : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (Csz : ℝ) (j : Fin D.R.m), 8 ≤ Csz → Sizes D j L.sc.b → (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ) - Csz * ((D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * (ofRecord D L Del h0).Lp) ≤ lowB D j L.sc.b := by
  intro D L Del h0 Csz j hC hS
  rw [sum_logHook_eq]
  have hLp : (ofRecord D L Del h0).Lp = GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D L.sc.b := by
    rw [Formalism.L2.DIV.NumTieH.Lp_eq]; rfl
  have hpos : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D L.sc.b := by
    have := (GlobalTheory.AdelicScalar.SizeBounds.sizes D j L.sc.b hS).1
    linarith
  rw [hLp]
  unfold GlobalTheory.BigOn.lowB
  have hX : 0 ≤ (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D L.sc.b := by positivity
  nlinarith

end GlobalTheory.LowMainTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableThetaKernelWeilRange
section
open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilThetaInt

theorem integrable_thetaKO : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (A B : HSp D) (m : Measure (GA D B)), m.IsHaarMeasure → 1 ≤ A.rank → (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ ω → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ g, Integrable (descend (GQ B) fun h => thetaKO ω g h f) (autMeasure B m) := by
  intro hP D A B m hm hA hw ψ χ ω hW f hf g
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨ν, 𝓨, hν⟩ := GlobalTheory.Size.exists_isCovolOne A B
  have hF := hW.om_pres (g, 1) f hf
  have hS : GlobalTheory.Core.Rk.SW.sch ψ A B ν 𝓨 (ω (g, 1) f) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ B.rank A.rank :=
    (GlobalTheory.SchSchwartzAll.schSchwartz D ψ hW.std θ hθ A B ν 𝓨 hν).1 _ hF
  have hfin := hP D A.rank B hA hw θ hθ m hm ⟨_, hS⟩
  have hleft := GlobalTheory.SiegelFormula.leftInv_thetaKO hW hf g
  have hcont : Continuous fun h => thetaKO ω g h f :=
    (hW.om_cont f hf 0).comp (Continuous.prodMk_right g)
  refine ⟨?_, ?_⟩
  · rw [autMeasure, aestronglyMeasurable_quotMeasure_iff_lift, hleft.lift_descend]
    exact hcont.aestronglyMeasurable
  · refine lt_of_le_of_lt (lintegral_mono fun q => ?_) hfin
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, GlobalTheory.SiegelFormula.absTheta]
    rw [GlobalTheory.StdUnn.thetaKO_eq_tsum_sch D ψ A B χ ω hW ν 𝓨 hν f hf g]
    exact enorm_tsum_le_tsum_enorm

end GlobalTheory.WeilThetaInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.BasicNotions.TH GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.FockBridge

section Ind

variable {T P : Type} [AddCommGroup T] [Module ℂ T] [AddCommGroup P] [Module ℂ P]

def Keeps (q : T →ₗ[ℂ] P) (L : Module.End ℂ T) : Prop := ∀ t, q t = 0 → q (L t) = 0

def indOp (q : T →ₗ[ℂ] P) (L : Module.End ℂ T) : Module.End ℂ P :=
  if h : Function.Surjective q ∧ Keeps q L then
    (q.quotKerEquivOfSurjective h.1).toLinearMap ∘ₗ
      ((LinearMap.ker q).mapQ (LinearMap.ker q) L fun t ht => LinearMap.mem_ker.2 (h.2 t (LinearMap.mem_ker.1 ht))) ∘ₗ
        (q.quotKerEquivOfSurjective h.1).symm.toLinearMap
  else 0

theorem indOp_apply {q : T →ₗ[ℂ] P} {L : Module.End ℂ T} (hq : Function.Surjective q) (hL : Keeps q L) (t : T) :
    indOp q L (q t) = q (L t) := by
  have e : (q.quotKerEquivOfSurjective hq).symm (q t) = Submodule.Quotient.mk t :=
    (LinearEquiv.symm_apply_eq _).2 (by simp)
  rw [indOp, dite_eq_left ⟨hq, hL⟩, LinearMap.comp_apply, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe]
  rw [e]
  rfl

theorem indOp_eq {q : T →ₗ[ℂ] P} {L : Module.End ℂ T} (hq : Function.Surjective q) (hL : Keeps q L)
    (M : Module.End ℂ P) (h : ∀ t, M (q t) = q (L t)) : indOp q L = M := by
  ext x
  obtain ⟨t, rfl⟩ := hq x
  rw [indOp_apply hq hL, h]

theorem keeps_mul {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (h : Keeps q L) (h' : Keeps q L') : Keeps q (L * L') :=
  fun t ht => h _ (h' t ht)

theorem keeps_sub {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (h : Keeps q L) (h' : Keeps q L') : Keeps q (L - L') :=
  fun t ht => by simp [h t ht, h' t ht]

theorem indOp_mul {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (hq : Function.Surjective q) (h : Keeps q L)
    (h' : Keeps q L') : indOp q (L * L') = indOp q L * indOp q L' :=
  indOp_eq hq (keeps_mul h h') _ fun t => by
    rw [Module.End.mul_apply, indOp_apply hq h', indOp_apply hq h]; rfl

theorem indOp_sub {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (hq : Function.Surjective q) (h : Keeps q L)
    (h' : Keeps q L') : indOp q (L - L') = indOp q L - indOp q L' :=
  indOp_eq hq (keeps_sub h h') _ fun t => by
    rw [LinearMap.sub_apply, indOp_apply hq h', indOp_apply hq h, LinearMap.sub_apply, map_sub]

end Ind

section Place

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem atPl_mul (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L * L') = atPl w L * atPl w L' := by
  unfold atPl
  rw [← PiTensorProduct.map_mul]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp only [Function.update_of_ne h]; first | rfl | simp [Module.End.mul_eq_comp]

theorem atPl_comm {w w' : ι} (hw : w ≠ w') (L : Module.End ℂ (V w)) (L' : Module.End ℂ (V w')) :
    atPl w L * atPl w' L' = atPl w' L' * atPl w L := by
  unfold atPl
  rw [← PiTensorProduct.map_mul, ← PiTensorProduct.map_mul]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp only [Function.update_self, Function.update_of_ne hw]; first | rfl | simp [Module.End.mul_eq_comp]
  · by_cases h' : i = w'
    · subst h'; simp only [Function.update_self, Function.update_of_ne h]; first | rfl | simp [Module.End.mul_eq_comp]
    · simp only [Function.update_of_ne h, Function.update_of_ne h']

end Place

section Fock

variable {F : Type} [Field F] [NumberField F] {P : Type} [AddCommGroup P] [Module ℂ P] {p₁ q₁ r s : ℕ}

def fockOp (q : Tens F p₁ q₁ r s →ₗ[ℂ] P) (w : InfinitePlace F) : Mat r s →ₗ[ℂ] Module.End ℂ P :=
  if h : Function.Surjective q ∧ ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y)) then
    { toFun := fun Y => indOp q (atPl w (fockAct2 p₁ q₁ r s Y))
      map_add' := fun Y Z => by
        apply indOp_eq h.1 (h.2 _)
        intro t
        rw [LinearMap.add_apply, indOp_apply h.1 (h.2 Y), indOp_apply h.1 (h.2 Z), map_add (f := _), Main.atPl_add,
          LinearMap.add_apply, map_add]
      map_smul' := fun c Y => by
        apply indOp_eq h.1 (h.2 _)
        intro t
        rw [RingHom.id_apply, LinearMap.smul_apply, indOp_apply h.1 (h.2 Y), map_smul, Main.atPl_smul,
          LinearMap.smul_apply, map_smul] }
  else 0

theorem fockOp_eq {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (Y : Mat r s) :
    fockOp q w Y = indOp q (atPl w (fockAct2 p₁ q₁ r s Y)) := by
  rw [fockOp, dite_eq_left ⟨hq, hK⟩]
  rfl

theorem fockOp_apply {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (Y : Mat r s) (t : Tens F p₁ q₁ r s) :
    fockOp q w Y (q t) = q (atPl w (fockAct2 p₁ q₁ r s Y) t) := by
  rw [fockOp_eq hq hK, indOp_apply hq (hK Y)]


variable (r s) in
def negT : Mat r s →ₗ[ℂ] Mat r s where
  toFun Y := -Yᵀ
  map_add' Y Z := by rw [Matrix.transpose_add, neg_add]
  map_smul' c Y := by rw [Matrix.transpose_smul, RingHom.id_apply, smul_neg]

theorem negT_apply (Y : Mat r s) : negT r s Y = -Yᵀ := rfl

def twAct (ε : Bool) (q : Tens F p₁ q₁ r s →ₗ[ℂ] P) (w : InfinitePlace F) : Mat r s →ₗ[ℂ] Module.End ℂ P :=
  if ε then fockOp q w else fockOp q w ∘ₗ negT r s

end Fock

section Frames

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def IsFrames (B : Base F E) {n d : ℕ} (Y : Spc F E n) (W : Spc F E d) {p₁ q₁ r s : ℕ}
    (A : InfinitePlace F → Matrix (Fin n) (Ix p₁ q₁) ℂ) (C : InfinitePlace F → Matrix (Fin d) (Ix r s) ℂ) : Prop :=
  Framed B.emb (incM F Y.J) (incM F W.J) 1 Complex.I A C ∧ (∀ w, Y.θ w * A w = A w * Jm p₁ q₁) ∧
    ∀ w, W.θ w * C w = C w * Jm r s

def IsFockData (B : Base F E) {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) {p₁ q₁ r s : ℕ}
    (A : InfinitePlace F → Matrix (Fin n) (Ix p₁ q₁) ℂ) (C : InfinitePlace F → Matrix (Fin d) (Ix r s) ℂ)
    (Φ : Tens F p₁ q₁ r s →ₗ[ℂ] SInf F (Fin n × Fin d)) : Prop :=
  IsFrames B Y W A C ∧ IsFockMap B.ψ B.emb M.co A C Φ

def IsAdaptedFrame (B : Base F E) {d d₁ : ℕ} (H' : Plane E d d₁) {r s : ℕ}
    (C : InfinitePlace F → Matrix (Fin d) (Ix r s) ℂ) (r₀ : Fin r) (s₀ : Fin s) : Prop :=
  ∀ w, (∃ c : ℂ, c ≠ 0 ∧ ∀ i, (B.emb w).1 (H'.x i) = c * (C w i (.inl r₀) + C w i (.inr s₀))) ∧
    (∃ c₁ c₂ : ℂ, ∀ i, (B.emb w).1 (H'.y i) = c₁ * C w i (.inl r₀) + c₂ * C w i (.inr s₀)) ∧
    ∀ a, a ≠ .inl r₀ → a ≠ .inr s₀ → ∃ z : Fin d₁ → ℂ, ∀ i, C w i a = (H'.ι.map (B.emb w).1 *ᵥ z) i

end Frames

section Laws

variable {F : Type} [Field F] [NumberField F] {P : Type} [AddCommGroup P] [Module ℂ P] {p₁ q₁ r s : ℕ}

theorem atPl_sub {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L - L') = atPl w L - atPl w L' := by
  simp only [Main.atPl_eq, MultilinearMap.map_update_sub]

theorem fockOp_lie {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (Y Z : Mat r s) :
    fockOp q w (Y * Z - Z * Y) = fockOp q w Y * fockOp q w Z - fockOp q w Z * fockOp q w Y := by
  rw [fockOp_eq hq hK, fockOp_eq hq hK, fockOp_eq hq hK, (GlobalTheory.FockPair.pair_lie_commute p₁ q₁ r s).2.1 Y Z,
    atPl_sub, atPl_mul, atPl_mul, indOp_sub hq (keeps_mul (hK Y) (hK Z)) (keeps_mul (hK Z) (hK Y)),
    indOp_mul hq (hK Y) (hK Z), indOp_mul hq (hK Z) (hK Y)]

theorem fockOp_comm {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} (hq : Function.Surjective q)
    (hK : ∀ w Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) {w w' : InfinitePlace F} (hw : w ≠ w') (Y Z : Mat r s) :
    fockOp q w Y * fockOp q w' Z = fockOp q w' Z * fockOp q w Y := by
  rw [fockOp_eq hq (hK w), fockOp_eq hq (hK w'), ← indOp_mul hq (hK w Y) (hK w' Z),
    ← indOp_mul hq (hK w' Z) (hK w Y), atPl_comm hw]

theorem negT_negT (Y : Mat r s) : negT r s (negT r s Y) = Y := by
  simp [negT_apply]

theorem negT_lie (Y Z : Mat r s) : negT r s (Y * Z - Z * Y) = negT r s Y * negT r s Z - negT r s Z * negT r s Y := by
  simp only [negT_apply, Matrix.transpose_sub, Matrix.transpose_mul, neg_mul_neg, neg_sub]

theorem sameBlock_symm {a b : Ix r s} (h : sameBlock a b) : sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

theorem isKC_negT {Y : Mat r s} (hY : IsKC Y) : IsKC (negT r s Y) := fun a b hab => by
  rw [negT_apply, Matrix.neg_apply, Matrix.transpose_apply, hY b a fun h => hab (sameBlock_symm h), neg_zero]

theorem negT_Eab (a b : Ix r s) : negT r s (Eab a b) = -Eab b a := by
  rw [negT_apply, Eab, Eab, Matrix.transpose_single]

theorem twAct_lie {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} {w : InfinitePlace F} (hq : Function.Surjective q)
    (hK : ∀ Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (ε : Bool) (Y Z : Mat r s) :
    twAct ε q w (Y * Z - Z * Y) = twAct ε q w Y * twAct ε q w Z - twAct ε q w Z * twAct ε q w Y := by
  cases ε
  · simp only [twAct, Bool.false_eq_true, if_false, LinearMap.comp_apply]
    rw [negT_lie, fockOp_lie hq hK]
  · simp only [twAct, if_true]
    exact fockOp_lie hq hK Y Z

theorem twAct_comm {q : Tens F p₁ q₁ r s →ₗ[ℂ] P} (hq : Function.Surjective q)
    (hK : ∀ w Y, Keeps q (atPl w (fockAct2 p₁ q₁ r s Y))) (ε : Bool) {w w' : InfinitePlace F} (hw : w ≠ w')
    (Y Z : Mat r s) : twAct ε q w Y * twAct ε q w' Z = twAct ε q w' Z * twAct ε q w Y := by
  cases ε
  · simp only [twAct, Bool.false_eq_true, if_false, LinearMap.comp_apply]
    exact fockOp_comm hq hK hw _ _
  · simp only [twAct, if_true]
    exact fockOp_comm hq hK hw _ _

end Laws

end GlobalTheory.FockBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullRepTwist
section
noncomputable section

namespace GlobalTheory.TwistedRepresentationEmbedding

open Module

def twist {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] (ρ : Representation K G V) (χ : G →* Kˣ) :
    Representation K G V where
  toFun g := ((χ g : Kˣ) : K) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp only [map_mul, Units.val_mul, Module.End.mul_apply, LinearMap.smul_apply, map_smul, smul_smul]
    ring_nf

theorem twist_apply {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] (ρ : Representation K G V)
    (χ : G →* Kˣ) (g : G) (v : V) : twist ρ χ g v = ((χ g : Kˣ) : K) • ρ g v := rfl

def embV {K : Type} [Field K] (σ : K →+* ℂ) (N : ℕ) : (Fin N → K) →ₛₗ[σ] (Fin N → ℂ) where
  toFun v k := σ (v k)
  map_add' v w := by funext k; simp
  map_smul' a v := by funext k; simp

def repE {K G : Type} [Field K] [Group G] {N : ℕ} (σ : K →+* ℂ) (ρ : Representation K G (Fin N → K)) :
    Representation ℂ G (Fin N → ℂ) where
  toFun g := Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map σ)
  map_one' := by
    rw [map_one, LinearMap.toMatrix'_one, Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.toLin'_one]; rfl
  map_mul' g h := by
    rw [map_mul, LinearMap.toMatrix'_mul, Matrix.map_mul, Matrix.toLin'_mul]; rfl

theorem repE_embV {K G : Type} [Field K] [Group G] {N : ℕ} (σ : K →+* ℂ) (ρ : Representation K G (Fin N → K)) (g : G)
    (v : Fin N → K) : repE σ ρ g (embV σ N v) = embV σ N (ρ g v) := by
  funext k
  change (Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map σ)) (fun j => σ (v j)) k = σ (ρ g v k)
  have h := RingHom.map_mulVec σ (LinearMap.toMatrix' (ρ g)) v k
  rw [LinearMap.toMatrix'_mulVec] at h
  rw [Matrix.toLin'_apply, h]
  rfl

theorem embV_single {K : Type} [Field K] (σ : K →+* ℂ) (N : ℕ) (k : Fin N) :
    embV σ N (Pi.single k 1) = Pi.single k 1 := by
  funext j
  change σ ((Pi.single k (1 : K) : Fin N → K) j) = (Pi.single k (1 : ℂ) : Fin N → ℂ) j
  by_cases h : j = k
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem embV_li {K : Type} [Field K] (σ : K →+* ℂ) (N : ℕ) :
    LinearIndependent ℂ fun k => embV σ N (Pi.single k 1) := by
  convert (Pi.basisFun ℂ (Fin N)).linearIndependent using 1
  funext k
  simp [embV_single]

theorem embV_span {K : Type} [Field K] (σ : K →+* ℂ) (N : ℕ) :
    Submodule.span ℂ (Set.range (embV σ N)) = ⊤ := by
  refine eq_top_iff.2 ((Pi.basisFun ℂ (Fin N)).span_eq.ge.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  exact ⟨Pi.single k 1, by simp [embV_single]⟩

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem isPullRep_twist {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U]
    [MulAction U C] {M : TwoLevels E r U C} {la : Wt M.Ψ r} {ρ : Representation ℂ U (M.cusp la)}
    (h : IsPullRep M la ρ) (χ : U →* ℂˣ) : IsPullRep M la (twist ρ χ) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨fun u c => χ u⁻¹ * a u c, fun u F hF c x => ?_⟩
  rw [twist_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, ha u F hF c x]
  simp [mul_assoc]

end GlobalTheory.TwistedRepresentationEmbedding

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTotallySplitRationalPrimeOfSplitsCompletely
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.SplitLevelsBall

theorem setOf_prime_mem_eq_primesOver (E : Type) [Field E] [NumberField E] (g : ℕ) (hg : g.Prime) :
    {P : Ideal (𝓞 E) | P.IsPrime ∧ (g : 𝓞 E) ∈ P} = (Ideal.span {(g : ℤ)}).primesOver (𝓞 E) := by
  ext P
  simp only [Set.mem_setOf_eq, Ideal.primesOver, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hP, hgP⟩
    refine ⟨hP, ⟨?_⟩⟩
    have hmax : (Ideal.span {(g : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hg).irreducible
    have hle : Ideal.span {(g : ℤ)} ≤ P.under ℤ := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show (g : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) P
      rw [Ideal.mem_comap, map_natCast]
      exact hgP
    have hne : P.under ℤ ≠ ⊤ := (Ideal.IsPrime.comap (f := algebraMap ℤ (𝓞 E)) (hK := hP)).ne_top
    exact hmax.eq_of_le hne hle
  · rintro ⟨hP, hlo⟩
    refine ⟨hP, ?_⟩
    have : (g : ℤ) ∈ P.under ℤ := by
      rw [← hlo.over]; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.under, Ideal.mem_comap] using this

theorem isTotallySplitPrime_of_splitsCompletely :
    ∀ (E : Type) [Field E] [NumberField E] (g : ℕ), SplitsCompletely E g → GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g := by
  intro E _ _ g ⟨hg, hc⟩
  exact ⟨hg, by rw [← setOf_prime_mem_eq_primesOver E g hg]; exact hc⟩

end GlobalTheory.SplitLevelsBall
end

