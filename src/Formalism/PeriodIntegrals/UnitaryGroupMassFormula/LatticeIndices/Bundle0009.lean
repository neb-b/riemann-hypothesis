module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.T2SpaceScalarTensorExt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.MemLocFrom

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatOpenCompact
section
noncomputable section

namespace MassDataIdxK

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

theorem latImage (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hfg : L.FG) :
    ∃ (m : ℕ) (b : Fin m → (Fin n → Fv F v ⊗[F] E)),
      (∀ i, b i ∈ latLoc (E := E) v (L : Set (Fin n → E))) ∧
      Submodule.span (Fv F v) (Set.range b) = ⊤ ∧
      (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) =
        (fun c : Fin m → Fv F v => ∑ i, c i • b i) ''
          Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hfg.restrictScalars (R := ℤ))
  have hsL : ∀ i, s i ∈ L := fun i => by
    have : s i ∈ Submodule.span ℤ (Set.range s) := Submodule.subset_span ⟨i, rfl⟩
    rw [hs] at this; exact this
  set b : Fin m → (Fin n → Fv F v ⊗[F] E) := fun i => ratV (F := F) (Fv F v) (s i) with hb
  have hlat : latLoc (E := E) v (L : Set (Fin n → E)) =
      Submodule.span (v.adicCompletionIntegers F) (Set.range b) := by
    apply le_antisymm
    · unfold latLoc
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; exact hx
      clear hx
      induction hx' using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
      | zero => rw [ratV_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [ratV_add]; exact add_mem hx hy
      | smul k x _ hx => rw [ratV_zsmul]; exact zsmul_mem hx k
    · unfold latLoc
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨s i, hsL i, rfl⟩
  have hbΛ : ∀ i, b i ∈ latLoc (E := E) v (L : Set (Fin n → E)) := fun i => by
    rw [hlat]; exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨m, b, hbΛ, ?_, ?_⟩
  · rw [eq_top_iff, ← spanTop v L hL, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have : ratV (F := F) (Fv F v) x ∈ latLoc (E := E) v (L : Set (Fin n → E)) :=
      Submodule.subset_span ⟨x, hx, rfl⟩
    rw [hlat] at this
    exact Submodule.span_le_restrictScalars (v.adicCompletionIntegers F) (Fv F v) _ this
  · ext x
    rw [SetLike.mem_coe, hlat, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨fun i => (c i : Fv F v), fun i _ => (c i).2, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨fun i => ⟨d i, hd i (Set.mem_univ _)⟩, rfl⟩

theorem latOpenCompact (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) :
    IsOpen (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) ∧
      IsCompact (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  obtain ⟨m, b, -, hsp, heq⟩ := latImage v L hL hfg
  let Φ : (Fin m → Fv F v) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E) :=
    { toFun := fun c => ∑ i, c i • b i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by simp [Finset.smul_sum, smul_smul] }
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    simp [Φ, Pi.single_apply]
  have himg : (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) =
      Φ '' Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := heq
  rw [himg]
  refine ⟨IsModuleTopology.isOpenMap_of_surjective hsurj _
    (isOpen_set_pi Set.finite_univ fun i _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v), ?_⟩
  exact (isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).image
    (IsModuleTopology.continuous_of_linearMap Φ)

end MassDataIdxK
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfLocalMod
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm
open scoped TensorProduct Matrix

section Loc

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def OEp (p : TypX X) : Set (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) :=
  PI.FinKW.psiV X.B.I p.1 '' (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E : Set _)

def InModP (p : TypX X) (m : ℕ) (S : Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E))
    (y : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) : Prop :=
  y ∈ Submodule.span (p.1.adicCompletionIntegers X.B.I.F) {w | ∃ t ∈ OEp X p, ∃ s ∈ S, w = t • s} ⊔
    Ideal.span {((m : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} •
      latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def LocCong (p : TypX X) (y : HAp X p) : Prop :=
  (∀ a : Fin D.R.rS, InModP X p X.B.g ((fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) '' {b | b.1 < a.1})
      (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J y :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I p.1 (X.e0 a))) ∧
  InModP X p X.B.g (Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b))
      (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J y :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I p.1 X.z0) ∧
  ∀ i : Fin D.R.k, InModP X p X.B.g ((Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) ∪
      (fun j => PI.FinKW.vecV X.B.I p.1 (X.bw j)) '' {j | j.1 < i.1})
      (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J y :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I p.1 (X.bw i))

def StImAloc (p : TypX X) : Prop := KppX X hb p = {y | y ∈ KvX X p ∧ LocCong X p y}

end Loc

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.RowFlagIff
section
noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni)

variable {K : Type} [Field K] {r k : ℕ}

def pf (b : Fin (r + 1)) : Idx r k := if h : (b : ℕ) < r then Sum.inr (Sum.inr (Fin.rev ⟨b, h⟩)) else zI

def RowFlag (m : Matrix (Idx r k) (Idx r k) K) : Prop :=
  ∀ b : Fin (r + 1), mᵀ *ᵥ Pi.single (pf b) 1 - Pi.single (pf b) 1 ∈
    Submodule.span K ((fun a => Pi.single (pf (k := k) a) (1 : K)) '' {a | a < b})

theorem rowFlag_iff' (m : Matrix (Idx r k) (Idx r k) K) :
    RowFlag m ↔ ∀ b : Fin (r + 1), ∀ i, (∀ a, a < b → i ≠ pf a) →
      m (pf b) i = if i = pf b then 1 else 0 := by
  classical
  unfold RowFlag
  refine forall_congr' fun b => ?_
  have himg : (fun a => Pi.single (pf (k := k) a) (1 : K)) '' {a | a < b} =
      (fun j => Pi.single j (1 : K)) '' (pf '' {a | a < b}) := by
    rw [Set.image_image]
  rw [himg, mem_span_single]
  refine forall_congr' fun i => ?_
  have h1 : i ∉ pf '' {a | a < b} ↔ ∀ a, a < b → i ≠ pf a := by
    simp only [Set.mem_image, Set.mem_setOf_eq, not_exists, not_and]
    exact forall_congr' fun a => imp_congr_right fun _ => ne_comm
  rw [h1]
  refine imp_congr_right fun _ => ?_
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, sub_eq_zero, Matrix.transpose_apply]

theorem pf_castSucc (i : Fin r) : pf (k := k) (Fin.castSucc i) = Sum.inr (Sum.inr (Fin.rev i)) := by
  have h : ((Fin.castSucc i : Fin (r + 1)) : ℕ) < r := i.isLt
  unfold pf
  rw [dite_eq_left h]
  rfl

theorem pf_last : pf (r := r) (k := k) (Fin.last r) = zI := by
  unfold pf
  rw [dite_eq_right (by simp)]

theorem pf_of_lt {a b : Fin (r + 1)} (h : a < b) :
    pf (k := k) a = Sum.inr (Sum.inr (Fin.rev ⟨a, by have := b.isLt; omega⟩)) := by
  unfold pf
  rw [dite_eq_left (by omega)]

theorem rowFlag_iff (m : Matrix (Idx r k) (Idx r k) K) : RowFlag m ↔ RowC m := by
  classical
  rw [rowFlag_iff']
  constructor
  · intro H
    have Hr : ∀ (j : Fin r) (i : Idx r k), (∀ a : Fin r, a < j → i ≠ Sum.inr (Sum.inr (Fin.rev a))) →
        m (Sum.inr (Sum.inr (Fin.rev j))) i = if i = Sum.inr (Sum.inr (Fin.rev j)) then 1 else 0 := by
      intro j i hi
      have := H (Fin.castSucc j) i (fun a ha => by
        rw [pf_of_lt ha]
        exact hi _ (by rw [Fin.lt_def] at ha ⊢; simpa using ha))
      rwa [pf_castSucc] at this
    have Hz : ∀ i : Idx r k, (∀ a : Fin r, i ≠ Sum.inr (Sum.inr (Fin.rev a))) →
        m zI i = if i = zI then 1 else 0 := by
      intro i hi
      have := H (Fin.last r) i (fun a ha => by
        rw [pf_of_lt ha]
        exact hi _)
      rwa [pf_last] at this
    have Hf : ∀ (a : Fin r) (i : Idx r k), (∀ b : Fin r, i = Sum.inr (Sum.inr b) → b ≤ a) →
        m (Sum.inr (Sum.inr a)) i = if i = Sum.inr (Sum.inr a) then 1 else 0 := by
      intro a i hi
      have := Hr (Fin.rev a) i (fun c hc h => by
        have hle := hi _ h
        rw [Fin.le_def, Fin.val_rev] at hle
        rw [Fin.lt_def, Fin.val_rev] at hc
        have := a.isLt
        have := c.isLt
        omega)
      simpa only [Fin.rev_rev] using this
    unfold RowC IsUpUni
    refine ⟨⟨?_, fun a => ?_⟩, ?_, ?_, fun w => ?_, ?_, fun j => ?_⟩
    · intro a b hab
      have hab' : b < a := hab
      have := Hf a (Sum.inr (Sum.inr b)) (fun c h => by
        cases h
        exact hab'.le)
      simpa [b33, hab'.ne] using this
    · have := Hf a (Sum.inr (Sum.inr a)) (fun c h => by
        cases h
        exact le_rfl)
      simpa [b33] using this
    · ext a b
      simpa [b31] using Hf a (Sum.inl b) (fun c h => absurd h Sum.inl_ne_inr)
    · ext a x
      simpa [b32] using Hf a (Sum.inr (Sum.inl x)) (fun c h => by simp at h)
    · simpa [wI, zI] using Hz (wI w) (fun a h => by simp [wI] at h)
    · simpa using Hz zI (fun a h => by simp [zI] at h)
    · simpa [zI] using Hz (Sum.inl j) (fun a h => Sum.inl_ne_inr h)
  · intro hC
    unfold RowC IsUpUni at hC
    obtain ⟨⟨hup, hdiag⟩, h31, h32, hw, hzz, hl⟩ := hC
    intro b i hi
    induction b using Fin.lastCases with
    | last =>
      rw [pf_last]
      rcases i with c | ((w | u) | j)
      · simpa [zI] using hl c
      · simpa [wI, zI] using hw w
      · cases u
        simpa [zI] using hzz
      · exact absurd (by rw [pf_castSucc, Fin.rev_rev]) (hi _ (Fin.castSucc_lt_last (Fin.rev j)))
    | cast j =>
      rw [pf_castSucc]
      rcases i with c | (x | j')
      · simpa [b31] using congrFun (congrFun h31 (Fin.rev j)) c
      · simpa [b32] using congrFun (congrFun h32 (Fin.rev j)) x
      · rcases lt_trichotomy j' (Fin.rev j) with h | h | h
        · have h0 : m (Sum.inr (Sum.inr (Fin.rev j))) (Sum.inr (Sum.inr j')) = 0 := hup h
          rw [h0, if_neg]
          simp [h.ne]
        · subst h
          simpa [b33] using hdiag (Fin.rev j)
        · have hlt : Fin.castSucc (Fin.rev j') < Fin.castSucc j := by
            rw [Fin.castSucc_lt_castSucc_iff, Fin.lt_def, Fin.val_rev]
            rw [Fin.lt_def, Fin.val_rev] at h
            have := j.isLt
            have := j'.isLt
            omega
          exact absurd (by rw [pf_castSucc, Fin.rev_rev]) (hi _ hlt)

end MassDataIdxStIm
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfParts
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X)

abbrev FpX : Type := Fv X.B.I.F p.1

abbrev TpX : Type := FpX X p ⊗[X.B.I.F] X.B.I.E

theorem card_idx : Fintype.card (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) = X.B.I.n := by
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]

  rw [X.n_eq]
  obtain ⟨a, ha⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  simp only [Formalism.BasicNotions.Ranks.rS, Formalism.BasicNotions.Ranks.r]
  omega

def idxEquiv : Fin X.B.I.n ≃ Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k :=
  Fintype.equivOfCardEq (by rw [card_idx X, Fintype.card_fin])

def IsSplitEquiv (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) : Prop :=
  ∀ t, θ (sigR (FpX X p) X.B.I.cm.sig t) = (θ t).swap

def th1 (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) : TpX X p →+* FpX X p :=
  (RingHom.fst (FpX X p) (FpX X p)).comp θ.toAlgHom.toRingHom

def th2 (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) : TpX X p →+* FpX X p :=
  (RingHom.snd (FpX X p) (FpX X p)).comp θ.toAlgHom.toRingHom

def J1 (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p) :=
  X.B.I.J.map (fun e => th1 X p θ (inclR (FpX X p) e))

def LatBasis (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (P : GL (Fin X.B.I.n) (FpX X p)) : Prop :=
  ∀ x : Fin X.B.I.n → TpX X p, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
    (∀ i, (Matrix.mulVec ((P⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p))
        fun j => th1 X p θ (x j)) i ∈ p.1.adicCompletionIntegers X.B.I.F) ∧
    (∀ i, (Matrix.mulVec (Matrix.transpose ((P : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) *
        Matrix.transpose (J1 X p θ))
        fun j => th2 X p θ (x j)) i ∈ p.1.adicCompletionIntegers X.B.I.F)

def StSplitLat : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧ ∃ P, LatBasis X p θ P

end Loc

def LatCore : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p),
    IsSplitEquiv X p θ → ∀ P, LatBasis X p θ P → StLatGL X p

theorem stRed_of_parts {D : D7} (X : HidaSetting D) (p : TypX X) (hR : StResZ X p) (hS : StSplitLat X p)
    (hC : LatCore) : StRed X p := by
  obtain ⟨θ, hθ, P, hP⟩ := hS
  have hL : StLatGL X p := hC X p θ hθ P hP
  obtain ⟨π, hπ, hker⟩ := hR
  intro K hK
  obtain ⟨ψ, hψ, hψk⟩ := hL K hK
  refine ⟨(Matrix.GeneralLinearGroup.map π).comp ψ, ?_, ?_⟩
  · intro M
    classical
    rcases subsingleton_or_nontrivial (ZMod (gOf p)) with hs | hs
    · refine ⟨1, ?_⟩
      apply Units.ext
      ext i j
      exact @Subsingleton.elim _ hs _ _

    let A : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p) :=
      fun i j => Function.surjInv hπ ((M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) i j)
    have hA : ∀ i j, π (A i j) = (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) i j :=
      fun i j => Function.surjInv_eq hπ _
    have hdetM : IsUnit (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))).det :=
      by
        first
          | exact Matrix.isUnits_det_units M
          | exact (Matrix.isUnit_iff_isUnit_det (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)))).mp M.isUnit
    have hmap : π A.det = (M : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))).det := by
      rw [RingHom.map_det]
      congr 1
      ext i j
      exact hA i j
    have hle : RingHom.ker π ≤ IsLocalRing.maximalIdeal (Op X p) :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π)
    have hdet : IsUnit A.det := by
      by_contra hnu
      have hm : A.det ∈ IsLocalRing.maximalIdeal (Op X p) :=
        (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
      obtain ⟨v, hv⟩ := IsUnit.exists_right_inv (show IsUnit (π A.det) by rw [hmap]; exact hdetM)
      obtain ⟨b, rfl⟩ := hπ v
      have h1 : A.det * b - 1 ∈ RingHom.ker π := by
        rw [RingHom.mem_ker, RingHom.map_sub, map_mul, hv, map_one, sub_self]
      have h2 : A.det * b ∈ IsLocalRing.maximalIdeal (Op X p) := by
        first
          | exact Ideal.mul_mem_right _ _ hm
          | exact Ideal.mul_mem_right _ hm
      have h3 : (1 : Op X p) ∈ IsLocalRing.maximalIdeal (Op X p) := by
        have h4 := Ideal.sub_mem _ h2 (hle h1)
        rwa [sub_sub_cancel] at h4
      exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h3)) isUnit_one
    obtain ⟨x, hx⟩ := hψ ((Matrix.isUnit_iff_isUnit_det A).mpr hdet).unit
    refine ⟨x, ?_⟩
    apply Units.ext
    ext i j
    rw [MonoidHom.comp_apply, hx]
    exact hA i j
  · intro x

    have key : ∀ i j, π (((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p)) - 1) i j) =
        ((Matrix.GeneralLinearGroup.map π (ψ x) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) - 1) i j := by
      intro i j
      rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp only [map_one, map_zero] <;> rfl
    rw [← hψk x, ← hker]
    constructor
    · intro h i j
      rw [RingHom.mem_ker, key]
      have h' : (Matrix.GeneralLinearGroup.map π (ψ x) : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) = 1 := by
        rw [MonoidHom.comp_apply] at h
        rw [h]
        rfl
      rw [h', sub_self]
      rfl
    · intro h
      apply Units.ext
      ext i j
      have h0 := h i j
      rw [RingHom.mem_ker, key, Matrix.sub_apply, sub_eq_zero] at h0
      exact h0

end MassDataIdxSteps
end
end

