module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PartnersFactorsOfKernelSmith
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SmithPairing
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ChainDim

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinalTheorems
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def topOdd (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : X.TT :=
  ⟨segPos X.TT j i, (pos_mem X.TT j i).1⟩

def topEnd (X : Loc) (j : Fin (numSeg X.TT)) : X.TT :=
  ⟨segNext X.TT j, (next_mem X.TT j).1⟩

def symVar (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :
    BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → (X.TT × Bool) × Fin (X.m + 1)
  | Sum.inl (a, c) =>
    if h : (a : ℕ) < 2 * segS X.TT j then
      ((topOdd X j ⟨(a : ℕ) / 2, by omega⟩, decide ((a : ℕ) % 2 = 0)), c.succ)
    else ((topEnd X j, decide ((a : ℕ) = 2 * segS X.TT j)), c.succ)
  | Sum.inr (l, b) =>
    if h : (l : ℕ) < (X.seg C0 CE1 CE2 j).t then
      ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) ⟨l, h⟩), !b), 0)
    else ((topEnd X j, !b), 0)

def symLev (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :
    BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ
  | Sum.inl (a, _) =>
    if h : (a : ℕ) < 2 * segS X.TT j then (X.seg C0 CE1 CE2 j).P p ⟨(a : ℕ) / 2, by omega⟩ else 1
  | Sum.inr (l, _) =>
    if h : (l : ℕ) < (X.seg C0 CE1 CE2 j).t then (X.seg C0 CE1 CE2 j).P p (uTop (X.seg C0 CE1 CE2 j) ⟨l, h⟩) else 1

def digitMon (K : Type*) [CommSemiring K] (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  ∏ i : Fin (segS X.TT j), ∏ c : Fin (X.m + 1),
    MvPolynomial.X ((topOdd X j i, true), c) ^ b.rz i c * MvPolynomial.X ((topOdd X j i, false), c) ^ b.ry i c

def sTopMon (K : Type*) [CommSemiring K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  ∏ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
    MvPolynomial.X ((topOdd X j i, true), 0) ^ ((X.seg C0 CE1 CE2 j).P p i * (coarseA p (X.seg C0 CE1 CE2 j) b i - b.w i)) *
      MvPolynomial.X ((topOdd X j i, false), 0) ^ ((X.seg C0 CE1 CE2 j).P p i * b.sg i)
  else 1

def ioBlock (K : Type*) [CommRing K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (u : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  digitMon K C0 CE1 CE2 X j b * sTopMon K p C0 CE1 CE2 X j b *
    aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^
      symLev p C0 CE1 CE2 X j v) u

def symFam (K : Type*) [CommRing K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc)
    (β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m)
    (s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  ∏ j, ioBlock K p C0 CE1 CE2 X j (β j) (s j)

def Lemma44At (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
    ∀ β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m,
      (∀ j, Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j)) →
    ∀ s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O),
      (∀ j, s j ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
        (13 * X.k * X.N1 * X.Q * (X.c : ℝ) + mm) (β j)).SSZ O (r := X.m)) →
      ∃ F ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT),
        InA (C (algebraMap O (KK O) (S.w ^ (∑ j, blockOrd X.p (X.seg C0 CE1 CE2 j) (β j)))) * F) ∧
        InWj S.w (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g F - symFam (KK O) X.p C0 CE1 CE2 X β s) X.c ∧
        ∀ g' : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g' →
          ratPlane X.p X.n' 1 g' ≠ ratPlane X.p X.n' 1 g → InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g' F X.c

def IsFlatTheta {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O) (φ : WF p n' ≃+* W) {m : ℕ} (TT : Finset (Fin n'))
    (aT bT : Fin n' → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (Θ : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
        ↥(VHH (m := m) Kf TT aT bT)) : Prop :=
  letI : Algebra (WF p n') O := algOfIdent jO φ
  (∀ F : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O),
      InA (O := O) (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) ↔
      Θ F ∈ HHL (O := O) ι σ TT aT bT (colSpan W h)) ∧
    (∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g →
      ∀ e : Edge W Qq (m + 1), IsEdgeBasis p 1 e (h * ((matQ φ g)⁻¹).transpose) →
        ∀ (F : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O)) (i : ℕ),
          InWjRg p n' O w 1 (hhLetters TT) g (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) i ↔
          Θ F ∈ scale (algebraMap O Kf w ^ (i : ℤ)) (ReHH p ι σ w TT aT bT e)) ∧
    ∀ e : Edge W Qq (m + 1), IsEdge p n' 1 e → e.src = colSpan W h →
      ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g ∧ IsEdgeBasis p 1 e (h * ((matQ φ g)⁻¹).transpose)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FockZeroRight
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem span_coe_basis {E : Type} [AddCommGroup E] [Module O E] (Λ : Submodule O E) {n : ℕ}
    (B : Module.Basis (Fin n) O Λ) : Submodule.span O (Set.range fun i => (B i : E)) = Λ := by
  have h : (Set.range fun i => (B i : E)) = Λ.subtype '' Set.range B := by
    rw [← Set.range_comp]
    rfl
  rw [h, Submodule.span_image, B.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem fock_zero_right {σ : Type} (F : MvPolynomial σ (KK O)) : fock F (0 : MvPolynomial σ (KK O)) = 0 := by
  simp [fock]

theorem smith_block {σ : Type} (Λ : Submodule O (MvPolynomial σ (KK O))) (hfg : Module.Finite O Λ) :
    ∃ (n : ℕ) (al be : Fin n → MvPolynomial σ (KK O)), (∀ i, al i ∈ Λ ∧ be i ∈ Λ) ∧
      (∀ i l, i ≠ l → fock (al i) (be l) = 0) ∧ LinearIndependent O al ∧
      Submodule.span O (Set.range al) = Λ ∧ Submodule.span O (Set.range be) = Λ := by
  classical
  haveI : Module.Free O Λ := Module.free_of_finite_type_torsion_free'
  let e := Module.finBasis O Λ
  obtain ⟨P, Q, hP, hQ, hd⟩ := Formalism.InvariantFactorPaths.KP.smithPairing O (KK O) (Module.finrank O Λ)
    (Matrix.of fun a c => fock (e a : MvPolynomial σ (KK O)) (e c : MvPolynomial σ (KK O)))
  have hPt : IsUnit P.transpose.det := by rw [Matrix.det_transpose]; exact hP
  let alB := e.map (Matrix.toLinearEquiv e P.transpose hPt)
  let beB := e.map (Matrix.toLinearEquiv e Q hQ)
  have hal : ∀ i, (alB i : MvPolynomial σ (KK O)) = ∑ a, P i a • (e a : MvPolynomial σ (KK O)) := fun i => by
    show ((Matrix.toLin e e P.transpose (e i) : Λ) : MvPolynomial σ (KK O)) = _
    rw [Matrix.toLin_self]
    simp [Matrix.transpose_apply]
  have hbe : ∀ l, (beB l : MvPolynomial σ (KK O)) = ∑ c, Q c l • (e c : MvPolynomial σ (KK O)) := fun l => by
    show ((Matrix.toLin e e Q (e l) : Λ) : MvPolynomial σ (KK O)) = _
    rw [Matrix.toLin_self]
    simp
  refine ⟨_, fun i => (alB i : MvPolynomial σ (KK O)), fun i => (beB i : MvPolynomial σ (KK O)),
    fun i => ⟨(alB i).2, (beB i).2⟩, fun i l hil => ?_, ?_, span_coe_basis Λ alB, span_coe_basis Λ beB⟩
  · have h := hd i l hil
    show fock (alB i : MvPolynomial σ (KK O)) (beB l : MvPolynomial σ (KK O)) = 0
    rw [hal, hbe, fock_bilin]
    rw [Matrix.mul_apply] at h
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul] at h
    rw [Finset.sum_comm] at h
    rw [← h]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul]
    ring
  · exact alB.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ)

theorem span_single {β E : Type} [DecidableEq β] [AddCommGroup E] [Module O E] (M : β → Submodule O E) (T : Finset β)
    (hM : ∀ b, b ∉ T → M b = ⊥) (n : β → ℕ) (al : ∀ b, Fin (n b) → E)
    (hspan : ∀ b, Submodule.span O (Set.range (al b)) = M b) :
    Submodule.span O (Set.range fun x : (Σ b : {b // b ∈ T}, Fin (n b.1)) =>
      (Pi.single x.1.1 (al x.1.1 x.2) : β → E)) = Submodule.pi Set.univ M := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_pi]
    intro i _
    beta_reduce
    by_cases h : i = x.1.1
    · subst h
      rw [Pi.single_eq_same, ← hspan]
      exact Submodule.subset_span ⟨x.2, rfl⟩
    · rw [Pi.single_eq_of_ne h]
      exact Submodule.zero_mem _
  · intro f hf
    rw [Submodule.mem_pi] at hf
    have hfT : f = ∑ b ∈ T, Pi.single b (f b) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_pi_single]
      split_ifs with hi
      · rfl
      · have h0 := hf i (Set.mem_univ i)
        rw [hM i hi, Submodule.mem_bot] at h0
        exact h0
    rw [hfT]
    refine Submodule.sum_mem _ fun b hb => ?_
    have hfb : f b ∈ Submodule.span O (Set.range (al b)) := by
      rw [hspan]
      exact hf b (Set.mem_univ b)
    have e : (Pi.single b (f b) : β → E) = LinearMap.single O (fun _ : β => E) b (f b) := rfl
    rw [e]
    have hmap := Submodule.mem_map_of_mem (f := LinearMap.single O (fun _ : β => E) b) hfb
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨⟨⟨b, hb⟩, i⟩, rfl⟩

end Gen


open Classical in
theorem smithData_seg {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p r : ℕ) [NeZero r] {s : ℕ}
    (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ)
    (hFG : ∀ b, Module.Finite O (blockLat O p r S aTop aPlus m b)) :
    ∃ (n : ℕ) (al be : Fin n → SegVs O r s S.t) (β : Fin n → SegBlock s r),
      SmithData (segForm O p r S) (segLat O p r S aTop aPlus m) n al be β := by
  have hfin := kf_kept_finite p r S aTop
  set T := hfin.toFinset with hT
  have hmemT : ∀ b, b ∈ T ↔ Kept p r S aTop b := fun b => by rw [hT, Set.Finite.mem_toFinset]; rfl
  let M : SegBlock s r → Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) :=
    fun b => if Kept p r S aTop b then blockLat O p r S aTop aPlus m b else ⊥
  have hMfg : ∀ b, Module.Finite O (M b) := fun b => by
    by_cases hb : Kept p r S aTop b
    · have e : M b = blockLat O p r S aTop aPlus m b := if_pos hb
      rw [e]; exact hFG b
    · have e : M b = ⊥ := if_neg hb
      rw [e]; infer_instance
  have hM0 : ∀ b, b ∉ T → M b = ⊥ := fun b hb => if_neg fun h => hb ((hmemT b).2 h)
  choose n al be hmem horth hli hsa hsb using fun b => smith_block (M b) (hMfg b)
  let ι := Σ b : {b // b ∈ T}, Fin (n b.1)
  let ev : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let AL : ι → SegVs O r s S.t := fun x => Pi.single x.1.1 (al x.1.1 x.2)
  let BE : ι → SegVs O r s S.t := fun x => Pi.single x.1.1 (be x.1.1 x.2)
  have hL : segLat O p r S aTop aPlus m = Submodule.pi Set.univ M := rfl
  have hALs : Submodule.span O (Set.range AL) = Submodule.pi Set.univ M := span_single M T hM0 n al hsa
  have hBEs : Submodule.span O (Set.range BE) = Submodule.pi Set.univ M := span_single M T hM0 n be hsb
  refine ⟨Fintype.card ι, AL ∘ ev.symm, BE ∘ ev.symm, fun i => (ev.symm i).1.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hL, ← hALs]
    refine ⟨Submodule.subset_span ⟨_, rfl⟩, ?_⟩
    rw [hALs, ← hBEs]
    exact Submodule.subset_span ⟨_, rfl⟩
  · intro i b hb
    exact ⟨Pi.single_eq_of_ne hb _, Pi.single_eq_of_ne hb _⟩
  · intro i l hil
    set x := ev.symm i with hx
    set y := ev.symm l with hy
    have hxy : x ≠ y := fun h => hil (ev.symm.injective h)
    show segForm O p r S (AL x) (BE y) = 0
    rw [segForm_eq_sum p r S {x.1.1} (AL x) (BE y) (fun b hb => Pi.single_eq_of_ne (by simpa using hb) _),
      Finset.sum_singleton]
    show _ * fock ((Pi.single x.1.1 (al x.1.1 x.2) : SegVs O r s S.t) x.1.1)
      ((Pi.single y.1.1 (be y.1.1 y.2) : SegVs O r s S.t) x.1.1) = 0
    rw [Pi.single_eq_same]
    by_cases hb : x.1.1 = y.1.1
    · obtain ⟨⟨xb, hxb⟩, xi⟩ := x
      obtain ⟨⟨yb, hyb⟩, yi⟩ := y
      simp only at hb
      subst hb
      rw [Pi.single_eq_same, horth xb xi yi (fun h => hxy (by rw [h])), mul_zero]
    · rw [Pi.single_eq_of_ne hb, fock_zero_right, mul_zero]
  · have h1 := Pi.linearIndependent_single (R := O) al hli
    have hj : Function.Injective (fun x : ι => (⟨x.1.1, x.2⟩ : Σ b, Fin (n b))) := by
      rintro ⟨⟨xb, hxb⟩, xi⟩ ⟨⟨yb, hyb⟩, yi⟩ h
      simp only [Sigma.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      rw [eq_of_heq h2]
    exact (h1.comp _ hj).comp _ ev.symm.injective
  · rw [hL, ← hALs, EquivLike.range_comp]
  · rw [hL, ← hBEs, EquivLike.range_comp]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegLow
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Finset

theorem finsum_classes {β γ : Type*} [DecidableEq γ] (K : β → Prop) (hfin : {b | K b}.Finite) (f : β → ℕ)
    (key : β → γ) (DC : Finset γ) (F : γ → β → ℕ) (G : β → ℕ)
    (hF1 : ∀ d b, K b → key b = d → F d b = f b) (hF0 : ∀ d b, ¬ (K b ∧ key b = d) → F d b = 0)
    (hG1 : ∀ b, K b → G b = f b) (hG0 : ∀ b, ¬ K b → G b = 0) :
    ∑ d ∈ DC, ∑ᶠ b, F d b ≤ ∑ᶠ b, G b := by
  classical
  have hFs : ∀ d, ∑ᶠ b, F d b = ∑ b ∈ hfin.toFinset, F d b := fun d => by
    apply finsum_eq_sum_of_support_subset
    intro b hb
    rw [Function.mem_support] at hb
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra hK
    exact hb (hF0 d b (fun h => hK h.1))
  have hGs : ∑ᶠ b, G b = ∑ b ∈ hfin.toFinset, G b := by
    apply finsum_eq_sum_of_support_subset
    intro b hb
    rw [Function.mem_support] at hb
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra hK
    exact hb (hG0 b hK)
  rw [hGs, Finset.sum_congr rfl (fun d _ => hFs d), Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b hb
  have hK : K b := (Set.Finite.mem_toFinset hfin).mp hb
  rw [hG1 b hK]

  have hcl : ∀ d ∈ DC, F d b = if d = key b then f b else 0 := fun d _ => by
    by_cases hd : d = key b
    · rw [if_pos hd, hF1 d b hK hd.symm]
    · rw [if_neg hd, hF0 d b (fun h => hd h.2.symm)]
  rw [Finset.sum_congr rfl hcl, Finset.sum_ite_eq']
  split_ifs <;> omega

def dset (m P g : ℕ) : Finset (Fin (m + 1) → ℕ) :=
  (Fintype.piFinset fun _ : Fin (m + 1) => Finset.range P).filter fun ρ => ∑ c, ρ c ≤ g ∧ P ∣ g - ∑ c, ρ c

theorem card_tuple (m n : ℕ) : (Finset.Nat.antidiagonalTuple (m + 1) n).card = sd m n := by
  have h := card_tuples (m + 1) n (Nat.succ_pos m)
  have e : {P : Fin (m + 1) → ℕ // ∑ i, P i = n} ≃ (Finset.Nat.antidiagonalTuple (m + 1) n) :=
    Equiv.subtypeEquivRight fun P => Finset.Nat.mem_antidiagonalTuple.symm
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe] at h
  rw [h]
  unfold sdXi sd
  congr 1

theorem digit_sum (m P g : ℕ) (hP : 0 < P) : ∑ ρ ∈ dset m P g, sd m ((g - ∑ c, ρ c) / P) = sd m g := by
  classical
  simp only [← card_tuple]

  have hdec : ∀ e : Fin (m + 1) → ℕ, ∑ c, e c = ∑ c, e c % P + P * ∑ c, e c / P := fun e => by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun c _ => (Nat.mod_add_div (e c) P).symm)
  have hmap : ∀ e ∈ Finset.Nat.antidiagonalTuple (m + 1) g, (fun c => e c % P) ∈ dset m P g := by
    intro e he
    rw [Finset.Nat.mem_antidiagonalTuple] at he
    have h := hdec e
    rw [he] at h
    simp only [dset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun c => Nat.mod_lt _ hP, le_of_le_of_eq (Nat.le_add_right _ _) h.symm, ?_⟩
    exact ⟨∑ c, e c / P, by rw [h, Nat.add_sub_cancel_left]⟩
  symm
  rw [Finset.card_eq_sum_card_fiberwise (s := Finset.Nat.antidiagonalTuple (m + 1) g) hmap]
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [dset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hρ
  obtain ⟨hρP, hρle, hρdvd⟩ := hρ
  apply Finset.card_nbij' (fun e c => e c / P) (fun q c => ρ c + P * q c)
  · intro e he
    rw [Finset.mem_coe, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at he
    obtain ⟨hsum, hmod⟩ := he
    rw [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple]
    have h := hdec e
    rw [hsum] at h
    have hr : ∑ c, e c % P = ∑ c, ρ c := by rw [← hmod]
    show ∑ c, e c / P = (g - ∑ c, ρ c) / P
    rw [h, hr, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hP]
  · intro q hq
    rw [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
    constructor
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hq, Nat.mul_div_cancel' hρdvd]
      omega
    · funext c
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hρP c)]
  · intro e he
    rw [Finset.mem_coe, Finset.mem_filter] at he
    funext c
    have h : e c % P = ρ c := congrFun he.2 c
    show ρ c + P * (e c / P) = e c
    rw [← h, Nat.mod_add_div]
  · intro q _
    funext c
    show (ρ c + P * q c) / P = q c
    rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt (hρP c), zero_add]

theorem symDim_nat (m g : ℕ) : symDim (m + 1) (g : ℤ) = sd m g := by
  unfold symDim sd
  have h1 : ¬ ((g : ℤ) < 0) := by omega
  rw [if_neg h1]
  first
    | rw [Int.toNat_natCast]
    | rw [Int.toNat_coe_nat]
    | simp only [Int.toNat_ofNat]
  congr 1 <;> omega

private theorem sum_prod_sd_digits_eq_prod_sd (m s : ℕ) (P bTop aTop : Fin s → ℕ) (hP : ∀ i, 0 < P i) :
    ∑ d ∈ (Fintype.piFinset fun i => dset m (P i) (bTop i)) ×ˢ (Fintype.piFinset fun i => dset m (P i) (aTop i)),
      ∏ i, sd m ((bTop i - ∑ c, d.1 i c) / P i) * sd m ((aTop i - ∑ c, d.2 i c) / P i) =
    ∏ i, sd m (bTop i) * sd m (aTop i) := by
  rw [Finset.sum_product]
  simp only [Finset.prod_mul_distrib]
  rw [← Finset.sum_mul_sum]
  congr 1
  · exact (Finset.prod_univ_sum (fun i => dset m (P i) (bTop i))
      (fun i ρ => sd m ((bTop i - ∑ c, ρ c) / P i))).symm.trans
      (Finset.prod_congr rfl fun i _ => digit_sum m (P i) (bTop i) (hP i))
  · exact (Finset.prod_univ_sum (fun i => dset m (P i) (aTop i))
      (fun i ρ => sd m ((aTop i - ∑ c, ρ c) / P i))).symm.trans
      (Finset.prod_congr rfl fun i _ => digit_sum m (P i) (aTop i) (hP i))

theorem segLow_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (h : LowAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    SegLowAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  unfold SegLowAt
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hC j m hm hmc
  classical
  have hp : 0 < X.p := by
    obtain ⟨⟨hY, hkY, -⟩, -⟩ := hH
    have hk : (1 : ℝ) ≤ X.k := by
      unfold Loc.k
      have := (Nat.cast_nonneg X.m : (0 : ℝ) ≤ X.m)
      linarith
    have h3 : 1 ≤ X.k ^ 2 * X.Y ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hk) (one_le_pow₀ hY)
    exact Nat.cast_pos.mp (show (0 : ℝ) < X.p by linarith)
  have hP : ∀ i, 0 < (X.seg C0 CE1 CE2 j).P X.p i := fun i => by
    unfold SegData.P
    exact pow_pos hp _
  have hdig : ∀ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock d.1 d.2) := by
    intro d hd
    rw [Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset] at hd
    obtain ⟨h1, h2⟩ := hd
    simp only [dset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at h1 h2
    exact ⟨fun i c => ⟨(h1 i).1 c, (h2 i).1 c⟩, fun i => (h1 i).2, fun i => (h2 i).2⟩
  have hmm : ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ, mmB C0 CE1 CE2 X j rz ry =
      symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p) *
        (∏ i, sd X.m (((X.seg C0 CE1 CE2 j).bTop i - ∑ c, rz i c) / (X.seg C0 CE1 CE2 j).P X.p i) *
          sd X.m (((segATop X.TT X.aT j) i - ∑ c, ry i c) / (X.seg C0 CE1 CE2 j).P X.p i)) * sd X.m (X.seg C0 CE1 CE2 j).bPlus := by
    intro rz ry
    simp only [mmB, dimMM, coarseA, coarseC, digitBlock, symDim_nat]
  have hsum : ∑ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))), mmB C0 CE1 CE2 X j d.1 d.2 =
      symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p) *
        (∏ i, sd X.m (X.bT (segPos X.TT j i)) * sd X.m (X.aT (segPos X.TT j i))) *
          sd X.m (X.bT (segNext X.TT j)) := by
    rw [Finset.sum_congr rfl (fun d _ => hmm d.1 d.2), ← Finset.sum_mul, ← Finset.mul_sum,
      sum_prod_sd_digits_eq_prod_sd X.m (segS X.TT j) (fun i => (X.seg C0 CE1 CE2 j).P X.p i) (X.seg C0 CE1 CE2 j).bTop (segATop X.TT X.aT j) hP]
    rfl
  have hcls : ∑ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))), rankOnDigits O C0 CE1 CE2 X j m d.1 d.2 ≤
      segRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m := by
    have hfin := kf_kept_finite X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j)
    exact finsum_classes (fun b => Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) hfin
      (fun b => blockRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m b)
      (fun b : SegBlock (segS X.TT j) X.m => (b.rz, b.ry)) ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i)))
      (fun d b => if Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b ∧ b.rz = d.1 ∧ b.ry = d.2 then
        blockRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m b else 0)
      (fun b => if Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b then
        blockRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m b else 0)
      (fun d b hK hk => by subst hk; exact if_pos ⟨hK, rfl, rfl⟩)
      (fun d b hn => if_neg fun ⟨hK, h1, h2⟩ => hn ⟨hK, Prod.ext h1 h2⟩)
      (fun b hK => if_pos hK) (fun b hK => if_neg hK)
  rw [← hsum, Nat.cast_sum, Finset.mul_sum]
  calc ∑ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))), lowFac C0 CE1 CE2 X j ⌈m⌉₊ * (mmB C0 CE1 CE2 X j d.1 d.2 : ℝ)
      ≤ ∑ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))), (rankOnDigits O C0 CE1 CE2 X j m d.1 d.2 : ℝ) :=
        Finset.sum_le_sum fun d hd => h X W Qq O Kf ι σ jO w hS hH hC j m hm hmc d.1 d.2 (hdig d hd)
    _ = ((∑ d ∈ ((Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((X.seg C0 CE1 CE2 j).bTop i)) ×ˢ
      (Fintype.piFinset fun i => dset X.m ((X.seg C0 CE1 CE2 j).P X.p i) ((segATop X.TT X.aT j) i))), rankOnDigits O C0 CE1 CE2 X j m d.1 d.2 : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ (segRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m : ℝ) := Nat.cast_le.mpr hcls

theorem restSegLow_of (h : RestLow) : RestSegLow := by
  unfold RestSegLow
  unfold RestLow at h
  exact TransportedAlt.mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc hh => segLow_of hh) h

end Formalism.MainNotions.ColumnSystems.Pf
end
end

