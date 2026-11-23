module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntSubIsLattice

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryPairMapsCompletedHomLatticeOntoTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatMoveStd

variable {D : D7}

theorem mt_mul'' (V : HSp D) (g g' : GA D V) : mt V (g * g') = mt V g * mt V g' := by
  show (matHom V (g * g')).1 = (matHom V g).1 * (matHom V g').1
  rw [map_mul, Units.val_mul]

theorem mt_one'' (V : HSp D) : mt V 1 = 1 := by
  show (matHom V 1).1 = 1
  rw [map_one, Units.val_one]

theorem cA_cA'' (x : AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a e =>
    show (a ⊗ₜ[D.host.F] D.sp.cm.sig (D.sp.cm.sig e)) = _
    rw [show D.sp.cm.sig (D.sp.cm.sig e) = e from star_star e]

theorem unitary (V : HSp D) (hg : V.gram = 1) (g : GA D V) :
    ((mt V g).map (cA D))ᵀ * mt V g = 1 := by
  have h : ((mt V g).map (cA D))ᵀ * V.gram.map (incA D) * mt V g = V.gram.map (incA D) :=
    (g : HR (AF D.host.F) D.sp.cm.sig V.gram).2
  rw [hg, Matrix.map_one (incA D) (map_zero _) (map_one _), Matrix.mul_one] at h
  exact h

theorem mt_inv_eq (V : HSp D) (hg : V.gram = 1) (g : GA D V) : mt V g⁻¹ = ((mt V g).map (cA D))ᵀ := by
  have h1 := unitary V hg g
  have h2 : mt V g * mt V g⁻¹ = 1 := by rw [← mt_mul'', mul_inv_cancel, mt_one'']
  calc mt V g⁻¹ = (((mt V g).map (cA D))ᵀ * mt V g) * mt V g⁻¹ := by rw [h1, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]


set_option synthInstance.maxHeartbeats 200000 in
theorem int_of_moves (V : HSp D) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hM : Moves V rfl g N) (x : Fin V.rank → D.host.E) (hx : x ∈ N) (i : Fin V.rank) :
    finPart D ((mt V g⁻¹ *ᵥ fun k => incA D (x k)) i) ∈ intAE D := by
  rw [GlobalTheory.SplitDec.int_iff]
  have := (hM x).1 hx i
  have e : toEAf D ((mt V g⁻¹ *ᵥ fun k => incA D (x k)) i) = (finM V rfl g⁻¹ *ᵥ fun j => eToEAf D (x j)) i := by
    simp only [Matrix.mulVec, dotProduct]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    rfl
  rw [e]; exact this

theorem gen_eq (α : Af D.host.F) (c x y : D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * x * y) = (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) * incA D x * incA D y := by
  simp [incA, inclR, Algebra.TensorProduct.tmul_mul_tmul]

end GlobalTheory.LatMoveStd

namespace GlobalTheory.LatMoveStd

variable {D : D7}


set_option synthInstance.maxHeartbeats 200000 in
theorem int_conj (V : HSp D) (hg : V.gram = 1) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hM : Moves V rfl g N) (s : Fin V.rank → D.host.E) (hs : s ∈ N) (j : Fin V.rank) :
    finPart D (∑ l, cA D (incA D (s l)) * mt V g l j) ∈ intAE D := by
  rw [← GlobalTheory.FinPl.FrameLat.cA_int_iff]
  have e : cA D (∑ l, cA D (incA D (s l)) * mt V g l j) = (mt V g⁻¹ *ᵥ fun k => incA D (s k)) j := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mt_inv_eq V hg g, map_sum]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, cA_cA'', mul_comm]
  rw [e]; exact int_of_moves V g N hM s hs j

theorem single_mem (S T : HSp D) (hgS : S.gram = 1) (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (c : D.host.E)
    (hc : c ∈ D.host.AA) (i0 : Fin T.rank) (j0 : Fin S.rank) :
    (Matrix.single i0 j0 (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) : WO S T) ∈
      latO S T (intVec D _) (intVec D _) (fun _ => True) := by
  have hint : ∀ {n : ℕ} (k : Fin n), Pi.single k (1 : D.host.E) ∈ intVec D n := by
    intro n k l
    by_cases h : l = k
    · subst h; rw [Pi.single_eq_same]; exact isIntegral_one
    · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
  refine AddSubgroup.subset_closure ⟨α, hα, fun _ h => absurd trivial h, c, hc, Pi.single j0 1, hint j0,
    Pi.single i0 1, hint i0, ?_⟩
  ext i j
  rw [Matrix.of_apply, hgS]
  have hsum : ∑ k, star ((Pi.single j0 (1 : D.host.E) : Fin S.rank → D.host.E) k) *
      (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E) k j =
      star ((Pi.single j0 (1 : D.host.E) : Fin S.rank → D.host.E) j) := by
    rw [Finset.sum_eq_single j (fun k _ hk => by rw [Matrix.one_apply_ne hk, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), Matrix.one_apply_eq, mul_one]
  rw [hsum]
  by_cases hi : i = i0
  · subst hi
    by_cases hj : j = j0
    · subst hj
      rw [Matrix.single_apply_same, Pi.single_eq_same, Pi.single_eq_same, star_one, mul_one, mul_one]
    · rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hj), Pi.single_eq_of_ne hj, star_zero, mul_zero,
        TensorProduct.tmul_zero]
  · rw [Matrix.single_apply_of_row_ne (Ne.symm hi), Pi.single_eq_of_ne hi, mul_zero, zero_mul,
      TensorProduct.tmul_zero]

end GlobalTheory.LatMoveStd

namespace GlobalTheory.LatMoveStd

variable {D : D7}

theorem row_one {n : ℕ} (s : Fin n → D.host.E) (l : Fin n) :
    ∑ m, star (s m) * (1 : Matrix (Fin n) (Fin n) D.host.E) m l = star (s l) := by
  rw [Finset.sum_eq_single l (fun k _ hk => by rw [Matrix.one_apply_ne hk, mul_zero])
    (fun h => absurd (Finset.mem_univ l) h), Matrix.one_apply_eq, mul_one]


set_option synthInstance.maxHeartbeats 200000 in
theorem gen_mem (S T : HSp D) (hgS : S.gram = 1) (hgT : T.gram = 1) (g : GA D S) (h : GA D T)
    (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hN : Moves S rfl g N) (hN' : Moves T rfl h N') (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (c : D.host.E)
    (hc : c ∈ D.host.AA) (s : Fin S.rank → D.host.E) (hs : s ∈ N) (t : Fin T.rank → D.host.E) (ht : t ∈ N') :
    actO S T g⁻¹ h⁻¹ (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j))
      ∈ latO S T (intVec D _) (intVec D _) (fun _ => True) := by
  have e1 : actO S T g⁻¹ h⁻¹
      (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j)) =
      Matrix.of fun i j => ((mt T h⁻¹ *ᵥ fun k => incA D (t k)) i * ∑ l, cA D (incA D (s l)) * mt S g l j) *
        (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) := by
    ext i j
    simp only [actO, inv_inv, Matrix.mul_apply, Matrix.of_apply, hgS, row_one, gen_eq,
      ← GlobalTheory.FinPl.FrameLat.cA_incA, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  rw [e1, Matrix.matrix_eq_sum_single ((Matrix.of fun i j =>
    ((mt T h⁻¹ *ᵥ fun k => incA D (t k)) i * ∑ l, cA D (incA D (s l)) * mt S g l j) *
        (pairA D.host.F 0 α ⊗ₜ[D.host.F] c)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))]
  refine sum_mem fun i0 _ => sum_mem fun j0 _ => ?_
  rw [Matrix.of_apply, ← smul_eq_mul, ← Matrix.smul_single]
  refine GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ?_ _ (single_mem S T hgS α hα c hc i0 j0)
  rw [map_mul]
  exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE (int_of_moves T h N' hN' t ht i0) (int_conj S hgS g N hN s hs j0)

end GlobalTheory.LatMoveStd

namespace GlobalTheory.LatMoveStd

theorem latO_moved_onto : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b), S.gram = 1 → T.gram = 1 → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), Moves S hS g N → Moves T hT h N' → ∀ u' ∈ latO S T (latFr S hS N) (latFr T hT N') (fun _ => True), ∃ u ∈ latO S T (intVec D _) (intVec D _) (fun _ => True), actO S T g h u = u' := by
  intro D S T a b hS hT hgS hgT g _ h _ N N' hN hN' u' hu'
  subst hS; subst hT
  refine ⟨actO S T g⁻¹ h⁻¹ u', ?_, ?_⟩
  · let Ψ : WO S T →+ WO S T :=
      { toFun := actO S T g⁻¹ h⁻¹
        map_zero' := by simp only [actO, Matrix.mul_zero, Matrix.zero_mul]
        map_add' := fun x y => by simp only [actO, Matrix.mul_add, Matrix.add_mul] }
    have key : latO S T (latFr S rfl N) (latFr T rfl N') (fun _ => True) ≤
        (latO S T (intVec D _) (intVec D _) (fun _ => True)).comap Ψ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨α, hα, -, c, hc, s, hs, t, ht, rfl⟩
      exact gen_mem S T hgS hgT g h N N' hN hN' α hα c hc s hs t ht
    exact key hu'
  · simp only [actO]
    rw [inv_inv, Matrix.mul_assoc (mt T h), Matrix.mul_assoc (mt T h⁻¹ * u'), ← mt_mul'', mul_inv_cancel, mt_one'', Matrix.mul_one,
      ← Matrix.mul_assoc, ← mt_mul'', mul_inv_cancel, mt_one'', Matrix.one_mul]

end GlobalTheory.LatMoveStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacTIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.VacAll

def MoveT {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (θ : InfFam (I.rec7 l Z)) (i : ℕ)
    (hi : i + 1 ≤ B.R.m) (c₀ : ℂ) (μ : (AE (I.rec7 l Z))ˣ →* Circle) (om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)))
    (vac : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ)
    (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) (h : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (i + 1))) : Prop :=
  ∀ N N', Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) g N → Moves _ (rankN (I.rec7 l Z) (i + 1) hi) h N' →
    ∀ x y, IsDetRoot _ g x → IsDetRoot _ h y →
      ColDat.xiS θ i hi (om (g, h) vac) = fun z => c₀ * (μ x : ℂ)⁻¹ * (μ y : ℂ) * I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N N' z

theorem vacT_iff {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {θ : InfFam (I.rec7 l Z)} {i : ℕ}
    {hi : i + 1 ≤ B.R.m} {c₀ : ℂ} {μ : (AE (I.rec7 l Z))ˣ →* Circle} {om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))}
    {vac : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ} :
    VacT I l Z θ i hi c₀ μ om vac ↔ ∀ g ∈ GfC _, ∀ h ∈ GfC _, MoveT I l Z θ i hi c₀ μ om vac g h := Iff.rfl

theorem xiS_smul {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (θ : InfFam (I.rec7 l Z)) (i : ℕ)
    (hi : i + 1 ≤ B.R.m) (c : ℂ) (F : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ) :
    ColDat.xiS θ i hi (c • F) = fun z => c * ColDat.xiS θ i hi F z := by
  funext z
  simp only [ColDat.xiS, xiN, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.AdForm.VacAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumMemSpanHeisenbergTranslatesOfNeZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacCyclic

theorem exists_mem_of_eigen {X ι U : Type} [AddCommGroup X] [Module ℂ X] (v : ι → X) (A : U → X →ₗ[ℂ] X) (χ : ι → U → ℂ)
    (hA : ∀ i u, A u (v i) = χ i u • v i) (hp : ∀ i j, (∀ u, χ i u = χ j u) → v i ∈ Submodule.span ℂ {v j})
    (W : Submodule ℂ X) (hW : ∀ u, ∀ x ∈ W, A u x ∈ W) (s : Finset ι) :
    ∀ f ∈ Submodule.span ℂ (v '' s), f ∈ W → f ≠ 0 → ∃ i, v i ∈ W := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  intro f hf hfW hf0

  have hrem : ∀ i ∈ s, ∀ u, A u f - χ i u • f ∈ Submodule.span ℂ (v '' (s.erase i : Finset ι)) := by
    intro i _ u
    have : Submodule.span ℂ (v '' s) ≤
        (Submodule.span ℂ (v '' (s.erase i : Finset ι))).comap (A u - χ i u • LinearMap.id) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      show A u (v j) - χ i u • v j ∈ Submodule.span ℂ (v '' (s.erase i : Finset ι))
      rw [hA, ← sub_smul]
      by_cases h : j = i
      · rw [h, sub_self, zero_smul]; exact zero_mem _
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, Finset.mem_coe.2 (Finset.mem_erase.2 ⟨h, hj⟩), rfl⟩)
    exact this hf
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp at hf; exact absurd hf hf0
  by_cases hall : ∀ j ∈ s, ∀ u, χ j u = χ i u
  · have : Submodule.span ℂ (v '' s) ≤ Submodule.span ℂ {v i} := by
      rw [Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      exact hp j i (hall j hj)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (this hf)
    have hc : c ≠ 0 := by rintro rfl; exact hf0 (zero_smul _ _)
    exact ⟨i, (W.smul_mem_iff hc).1 hfW⟩
  · push Not at hall
    obtain ⟨j, hj, u, hu⟩ := hall
    have hm : ∀ k, A u f - χ k u • f ∈ W := fun k => W.sub_mem (hW u f hfW) (W.smul_mem _ hfW)
    by_cases h0 : A u f - χ i u • f = 0
    · refine ih _ (Finset.erase_ssubset hj) _ (hrem j hj u) (hm j) fun h1 => hf0 ?_
      have : (χ j u - χ i u) • f = 0 := by
        rw [sub_smul, ← sub_eq_zero.1 h0, ← sub_eq_zero.1 h1, sub_self]
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hu)
    · exact ih _ (Finset.erase_ssubset hi) _ (hrem i hi u) (hm i) h0

theorem psi_ne_zero {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (x : A) : ψ x ≠ 0 := fun h => by
  have := ψ.map_add_eq_mul x (-x)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem fin_add {D : D7} {S T : HSp D} {a b : WO S T} (ha : a.map (infPart D) = 0) (hb : b.map (infPart D) = 0) :
    (a + b).map (infPart D) = 0 := by
  ext i j
  have h1 : infPart D (a i j) = 0 := congrFun (congrFun ha i) j
  have h2 : infPart D (b i j) = 0 := congrFun (congrFun hb i) j
  show infPart D (a i j + b i j) = 0
  rw [RingHom.map_add (f := _), h1, h2, add_zero]

theorem fin_neg {D : D7} {S T : HSp D} {a : WO S T} (ha : a.map (infPart D) = 0) : (-a).map (infPart D) = 0 := by
  ext i j
  have h1 : infPart D (a i j) = 0 := congrFun (congrFun ha i) j
  show infPart D (-a i j) = 0
  rw [RingHom.map_neg, h1, neg_zero]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem fin_zero : (0 : WO S T).map (infPart D) = 0 := by
  ext i j
  show infPart D (0 : AE D) = 0
  exact RingHom.map_zero _

theorem symplO_neg_right (u b : WO S T) : symplO S T u (-b) = -symplO S T u b := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← GlobalTheory.LatVac.symplO_add_right, neg_add_cancel, GlobalTheory.SplitScalar.symplO_zero_right]

theorem psi_diff {u a b : WO S T} (h : ψ (symplO S T u a) = ψ (symplO S T u b)) : ψ (symplO S T (-b + a) u) = 1 := by
  rw [GlobalTheory.SplitScalar.symplO_skew S T u, GlobalTheory.LatVac.symplO_add_right, symplO_neg_right, neg_add, neg_neg,
    ψ.map_add_eq_mul, ← h, ← ψ.map_add_eq_mul, add_neg_cancel, ψ.map_zero_eq_one]

theorem prop_of_eigen {a b : WO S T} {f₀ : WO S T → ℂ} {ε : ℂ} (h : heisO ψ S T (-b + a) f₀ = ε • f₀) :
    heisO ψ S T a f₀ ∈ Submodule.span ℂ {heisO ψ S T b f₀} := by
  have e := GlobalTheory.LatVac.heisO_heisO ψ b (-b + a) f₀
  rw [h, GlobalTheory.LatVac.heisO_smul, add_neg_cancel_left] at e
  refine (Submodule.smul_mem_iff _ (psi_ne_zero ψ (symplOH S T b (-b + a)))).1 ?_
  rw [← e]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem heis_mem_span {f x : WO S T → ℂ} {b : WO S T} (hb : b.map (infPart D) = 0)
    (hx : x ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f)) :
    heisO ψ S T b x ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hx
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← GlobalTheory.SplitScalar.heisL_apply, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [map_smul, GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.LatVac.heisO_heisO]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨b + a, fin_add hb a.2⟩, rfl⟩))

theorem mem_of_heis_mem {W : Submodule ℂ (WO S T → ℂ)} {f₀ : WO S T → ℂ} {a : WO S T}
    (h : heisO ψ S T (-a) (heisO ψ S T a f₀) ∈ W) : f₀ ∈ W := by
  rw [GlobalTheory.LatVac.heisO_heisO, neg_add_cancel, GlobalTheory.LatVac.heisO_zero] at h
  exact (W.smul_mem_iff (psi_ne_zero ψ _)).1 h

theorem mem_span_of_dual (Λ : AddSubgroup (WO S T)) (hfin : ∀ u ∈ Λ, u.map (infPart D) = 0)
    (hdual : ∀ u : WO S T, u.map (infPart D) = 0 → (∀ u' ∈ Λ, ψ (symplO S T u u') = 1) → u ∈ Λ) {f₀ f : WO S T → ℂ}
    (hε : ∀ u : Λ, ∃ ε : ℂ, ε ≠ 0 ∧ heisO ψ S T u f₀ = ε • f₀)
    (hf : f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀))
    (hf0 : f ≠ 0) :
    f₀ ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  choose ε hε0 hε using hε
  have hfW : f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) :=
    Submodule.subset_span ⟨⟨0, fin_zero⟩, GlobalTheory.LatVac.heisO_zero ψ f⟩
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
  have hfs : f ∈ Submodule.span ℂ ((fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀) '' c.support) := by
    rw [← hc]
    exact Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  obtain ⟨a, ha⟩ := exists_mem_of_eigen (fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀)
    (fun u : Λ => GlobalTheory.SplitScalar.heisL ψ S T u) (fun a u => ψ (symplO S T u a) * ε u)
    (fun a u => by
      rw [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisO_comm, hε, GlobalTheory.LatVac.heisO_smul, smul_smul])
    (fun a b h => prop_of_eigen (hε ⟨_, hdual _ (fin_add (fin_neg b.2) a.2) fun u hu =>
      psi_diff (mul_right_cancel₀ (hε0 ⟨u, hu⟩) (h ⟨u, hu⟩))⟩))
    _ (fun u x hx => by
      rw [GlobalTheory.SplitScalar.heisL_apply]
      exact heis_mem_span (hfin u u.2) hx) c.support f hfs hfW hf0
  exact mem_of_heis_mem (heis_mem_span (fin_neg a.2) ha)

theorem vac_mem_span : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {f₀ f : WO S T → ℂ}, IsVacO ψ θ S T sS sT ΛS ΛT f₀ → IsSelfDualC S ΛS → IsSelfDualC T ΛT → f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀) → f ≠ 0 → f₀ ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ f hv hS hT hf hf0
  obtain ⟨hdual, -, hsign⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hv.1 hS hT
  refine mem_span_of_dual _ (fun u hu => GlobalTheory.SplitScalar.latO_fin hu) (fun u hu h => (hdual u hu).2 h) (fun u => ?_) hf hf0
  obtain ⟨ε, h1, h2⟩ := hsign f₀ hv.2.lat u u.2
  refine ⟨ε, ?_, h2 f₀ hv.2.lat⟩
  rcases h1 with rfl | rfl <;> simp

end GlobalTheory.VacCyclic

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilActionEqSmulOfKeepsLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

noncomputable section
namespace GlobalTheory.LevLaw

theorem heisO_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (x : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
  funext t
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem omega_eq_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ vac Φ w, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) vac → IsSBHalf e (stdHom S T) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac Φ w → ∀ k ∈ GfC S, ∀ k' ∈ GfC T, (∀ x, x ∈ stdHom S T ↔ actO S T k k' x ∈ stdHom S T) → ∀ p q : ℂ, om (k, k') vac = p • vac → (∀ z, IsHalf e z → p * Φ (actO S T k⁻¹ k'⁻¹ z) = q * Φ z) → om (k, k') w = q • w := by
  intro D ψ θ S T a b hS hT δ sc hstd μ om hW e SS hSS vac Φ w hvac hΦ hw k hk k' hk' hkeep p q hp hq
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hSS
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hSS
  have sdS0 := GlobalTheory.SplitMove.selfDual_int S hstd.gS
  have sdT0 := GlobalTheory.SplitMove.selfDual_int T hstd.gT
  have hth : IsThetaFunO ψ S T vac := hvac.2.theta
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hw
  have th0 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hstd.std S T _ _ sdS0 sdT0 e hee hinf vac hth T₀ hT₀
  have pm := GlobalTheory.SplitMove.isPlaceModel_move₂ hW hkeep hT₀ th0
  rw [hp] at pm
  have omm : ∀ r s (X : WO S T → ℂ), om r (om s X) = om (r * s) X := fun r s X => by
    rw [map_mul]; rfl

  have hv0 : vac ≠ 0 := by
    intro h0
    obtain ⟨⟨m, hm⟩, hn⟩ := hvac.2.norm
    have h1 := hn m hm
    rw [h0] at h1
    simp [nrm2] at h1
  have hp0 : p ≠ 0 := by
    intro h0
    apply hv0
    have e1 : om (k⁻¹, k'⁻¹) (om (k, k') vac) = vac := by
      rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]; rfl
    rw [hp, h0, zero_smul, map_zero] at e1
    exact e1.symm
  set L := om (k, k') ∘ₗ T₀ ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T k k') with hL
  have pm2 : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac (p⁻¹ • L) := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, pm.trans Ψ hΨ x hx, heisO_smul]
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, pm.modul Ψ hΨ y hy, heisO_smul]
    · rw [LinearMap.smul_apply, pm.vac, smul_smul, inv_mul_cancel₀ hp0, one_smul]
  have w1 : w = T₀ Φ := hall T₀ hT₀
  have w2 : w = (p⁻¹ • L) Φ := hall _ pm2

  have hfun : q • (fun t => Φ (actO S T k k' t)) = p • Φ := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hz : IsHalf e (actO S T k k' z)
    · have h1 := hq _ hz
      rw [GlobalTheory.SplitHecke.actO_inv_actO] at h1
      exact h1.symm
    · have h2 : Φ (actO S T k k' z) = 0 := by
        by_contra hne; exact hz (hΦ.1 _ hne)
      have h3 : Φ z = 0 := by
        by_contra hne; exact hz (GlobalTheory.SplitHecke.isHalf_actO k k' (hΦ.1 _ hne))
      rw [h2, h3, mul_zero, mul_zero]
  have eL : L Φ = om (k, k') (T₀ fun t => Φ (actO S T k k' t)) := rfl
  calc om (k, k') w = om (k, k') (T₀ Φ) := by rw [← w1]
    _ = p⁻¹ • om (k, k') (T₀ (p • Φ)) := by
        rw [map_smul, map_smul, smul_smul, inv_mul_cancel₀ hp0, one_smul]
    _ = p⁻¹ • om (k, k') (T₀ (q • fun t => Φ (actO S T k k' t))) := by rw [hfun]
    _ = q • (p⁻¹ • L) Φ := by
        rw [map_smul, map_smul, LinearMap.smul_apply, eL, smul_comm]
    _ = q • w := by rw [← w2]

end GlobalTheory.LevLaw
end
end

