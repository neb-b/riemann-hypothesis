module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainOneLatticeClass
section
open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.SymChain.LatClass
open GlobalTheory.SymChain GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem valuation_lt_one_of_unif {ϖ : kˣ} (h : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) : valuation k (ϖ : k) < 1 :=
  (h _).2 le_rfl


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem irreducible_of_unif {ϖ : kˣ} (h : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) :
    Irreducible (⟨(ϖ : k), (valuation_lt_one_of_unif h).le⟩ : 𝒪[k]) := by
  have h1 := valuation_lt_one_of_unif h
  refine ⟨Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 h1, fun a b hab => ?_⟩
  by_contra hn
  rw [not_or] at hn
  have ha : valuation k (a : k) < 1 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hn.1
  have hb : valuation k (b : k) < 1 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hn.2
  have e : (ϖ : k) = (a : k) * b := congrArg Subtype.val hab
  have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
  have : valuation k (ϖ : k) < valuation k (ϖ : k) := by
    calc valuation k (ϖ : k) = valuation k (a : k) * valuation k (b : k) := by rw [e, map_mul]
      _ ≤ valuation k (ϖ : k) * valuation k (b : k) := mul_le_mul_left ((h _).1 ha) _
      _ < valuation k (ϖ : k) * 1 := mul_lt_mul_of_pos_left hb h0
      _ = _ := mul_one _
  exact lt_irrefl _ this

section
variable {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ}


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem chainLat_eq_latOf (ϖ : kˣ) (p : 𝒪[k]) (hp : (p : k) = ϖ) (o : ι ≃ n ⊕ Fin c) :
    chainLat p c (stdLat k n) = latOf (typeFrame ϖ o).bas := by
  ext y
  rw [mem_chainLat, mem_latOf_typeFrame, mem_stdLat, hp]
  refine and_congr Iff.rfl (forall_congr' fun i => ?_)
  have h0 : ((ϖ : k) ^ (i.val + 1)) ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  have hv : 0 < valuation k ((ϖ : k) ^ (i.val + 1)) := by simp [zero_lt_iff]
  constructor
  · rintro ⟨a, ha⟩
    rw [ha, map_mul]
    exact mul_le_of_le_one_left' a.2
  · intro h
    refine ⟨⟨y (.inr i) / (ϖ : k) ^ (i.val + 1), ?_⟩, by simp [div_mul_cancel₀ _ h0]⟩
    rw [Valuation.mem_integer_iff, map_div₀]
    exact (div_le_one₀ hv).2 h

end

section
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem act_latOf (u g : GL Y k) : act u (latOf g) = latOf (u * g) := by
  ext v
  rw [mem_act_iff_inv, ← mulVec_mem_latOf u, mulVec_mulVec, Units.mul_inv, one_mulVec]


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mapsInto_latOf_iff (g : GL Y k) (g' : GL Y' k) (x : Matrix Y Y' k) :
    MapsInto x (latOf g') (latOf g) ↔ IntM ((g⁻¹).val * x * g'.val) := by
  constructor
  · intro h i j
    have h1 : g'.val *ᵥ Pi.single j 1 ∈ latOf g' := by
      have := (mulVec_mem_latOf g' (g := 1) (y := Pi.single j 1)).2 (mem_latOf_one.2 fun l => by
        rw [Pi.single_apply]; split_ifs
        exacts [one_mem _, zero_mem _])
      rwa [mul_one] at this
    have := h _ h1 i
    rwa [mulVec_mulVec, mulVec_mulVec, mulVec_single_one] at this
  · intro h y hy i
    have : (g⁻¹).val *ᵥ (x *ᵥ y) = ((g⁻¹).val * x * g'.val) *ᵥ ((g'⁻¹).val *ᵥ y) := by
      simp [mulVec_mulVec, Matrix.mul_assoc]
    rw [this]
    exact sum_mem fun l _ => mul_mem (h i l) (hy l)

end

theorem oneClass_symChain (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (s κ : ℕ) (S : SymData k s κ)
    (t : Type) [Fintype t] [DecidableEq t] : S.OneClass t ν := by
  intro j c H h hf
  have h1 := valuation_lt_one_of_unif S.unif
  let p : 𝒪[k] := ⟨(S.ϖ : k), h1.le⟩
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1) (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)
  have e := chainLat_eq_latOf S.ϖ p rfl o
  have e' := chainLat_eq_latOf S.ϖ p rfl o'
  have hΦ : ∀ x, (S.T t).Phi j (c + 1) (by omega) x = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      (((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x).submatrix (ixSucc _ t j) id) := fun _ => rfl
  obtain ⟨r, hr, u, hu, hh⟩ := (oneCoset (n := XIx (Fin κ) t (j + 1)) (c := c + 1) (by omega)
    (irreducible_of_unif S.unif) S.cond hν (stdLat k (XIx (Fin κ) t j))).1 (S.μ (j + 1))
    ((S.T t).Phi j (c + 1) (by omega)) ((Chain.ofType_regular _ _ _ _ _).1 j (c + 1) _) (by
      intro x hx
      change MapsInto x (chainLat p _ _) (chainLat p _ _)
      rw [e, e', mapsInto_latOf_iff]
      rw [hΦ] at hx
      intro a b
      simpa [LatFrame.coords, typeFrame] using
        TypeDatum.intM_of_Phi_ne_zero _ _ hx ((ixSucc _ t j).symm (o.symm a)) (o'.symm b)) (by
      intro x y hy
      change MapsInto y (chainLat p _ _) (chainLat p _ _) at hy
      rw [e, e', mapsInto_latOf_iff] at hy
      rw [hΦ, hΦ]
      have : ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') (x + (S.ϖ : k) • y)).submatrix (ixSucc _ t j) id =
          ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x).submatrix (ixSucc _ t j) id +
          (S.ϖ : k) • ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') y).submatrix (ixSucc _ t j) id := by
        simp only [LatFrame.coords, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
        rfl
      refine (congrArg _ this).trans (TypeDatum.Phi_add _ (S.tame _) _ fun a b => ?_)
      rw [Matrix.smul_apply, smul_eq_mul, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 (hy _ _)) 1 h (act_one _) hf
  refine ⟨r, hr, u, mem_stabLat_iff.2 ?_, hh⟩
  change act u (chainLat p _ _) = chainLat p _ _ at hu
  rw [e, act_latOf] at hu
  exact hu

end GlobalTheory.SymChain.LatClass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainProjectedLevelOfPattern
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymChain.PrImage

section Plain
variable {k : Type*} [Field k] {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] {c : ℕ}

variable (k n c) in
def fixX : Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {v | ∀ r x, v.val r (.inl x) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inl x)}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro v w hv hw r x
    have : (v.val * w.val) r (.inl x) = (v.val * (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) r (.inl x) := by
      simp only [Matrix.mul_apply, hw _ x]
    rw [Units.val_mul, this, Matrix.mul_one, hv]
  inv_mem' := by
    intro v hv r x
    have : ((v⁻¹).val * v.val) r (.inl x) = ((v⁻¹).val * (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) r (.inl x) := by
      simp only [Matrix.mul_apply, hv _ x]
    rw [Matrix.mul_one, Units.inv_mul] at this
    exact this.symm

theorem N_le_fixX : N k n c 1 ≤ fixX k n c := by
  refine (Subgroup.closure_le _).2 fun g hg r x => hg r (.inl x) ?_
  rcases r with r | r <;> simp [RootEx.lev]

theorem embA_mem_fixX (D : GL (Fin c) k) : embA n D ∈ fixX k n c := by
  intro r x
  change (fromBlocks 1 0 0 D.val : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inl x) = _
  rcases r with r | r <;> simp [Matrix.one_apply]

theorem embX_mul_embA (g : GL n k) (D : GL (Fin c) k) : embX c g * embA n D = embA n D * embX c g := by
  refine Units.ext ?_
  change (fromBlocks g.val 0 0 1 * fromBlocks 1 0 0 D.val : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) =
    fromBlocks 1 0 0 D.val * fromBlocks g.val 0 0 1
  simp [fromBlocks_multiply]

theorem mul_embX_inl {w : GL (n ⊕ Fin c) k} (hw : w ∈ fixX k n c) (g : GL n k) (r : n ⊕ Fin c) (x : n) :
    (w * embX c g).val r (.inl x) = (embX c g).val r (.inl x) := by
  have : (w.val * (fromBlocks g.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) r (.inl x) =
      ((1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * (fromBlocks g.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k))
        r (.inl x) := by
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, hw r, fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero]
  rw [Matrix.one_mul] at this
  exact this

theorem embX_inr (g : GL n k) (r : n ⊕ Fin c) (i : Fin c) :
    (embX c g).val r (.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i) := by
  change (fromBlocks g.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i) = _
  rcases r with r | r <;> simp [Matrix.one_apply]

theorem conj_symm_apply (F : LatFrame k ι (n ⊕ Fin c)) (y : GL (n ⊕ Fin c) k) :
    F.conj.symm y = (reGL F.ord).symm (F.bas⁻¹ * y * F.bas) := by
  rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply]; simp [mul_assoc]

theorem entry_cases (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) {w : GL (n ⊕ Fin c) k} (hw : w ∈ fixX k n c) (g : GL n k)
    (a b : ι) :
    ((typeFrame ϖ o).conj.symm (embX c g)).val a b = ((typeFrame ϖ o).conj.symm (w * embX c g)).val a b ∨
      ((typeFrame ϖ o).conj.symm (embX c g)).val a b = (1 : Matrix ι ι k) a b := by
  obtain ⟨D, hD⟩ : ∃ D, (typeFrame ϖ o).bas = embA n D := ⟨_, rfl⟩
  have ho : (typeFrame ϖ o).ord = o := rfl
  have e1 : (embA n D)⁻¹ * embX c g * embA n D = embX c g := by
    rw [mul_assoc, embX_mul_embA, inv_mul_cancel_left]
  have e2 : (embA n D)⁻¹ * (w * embX c g) * embA n D = ((embA n D)⁻¹ * w * embA n D) * embX c g := by
    simp only [mul_assoc, embX_mul_embA]
  have hw' : (embA n D)⁻¹ * w * embA n D ∈ fixX k n c :=
    mul_mem (mul_mem (inv_mem (embA_mem_fixX D)) hw) (embA_mem_fixX D)
  rw [conj_symm_apply, conj_symm_apply, hD, ho, e1, e2, reGL_symm_val, reGL_symm_val, submatrix_apply,
    submatrix_apply, ← submatrix_one_equiv o, submatrix_apply]
  rcases o b with x | i
  · exact Or.inl (mul_embX_inl hw' g _ x).symm
  · exact Or.inr (embX_inr g _ i)

end Plain

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] {c : ℕ}

theorem prX_eq_comap (P : Level (GL ι k)) (Fr : ι → ι → Prop)
    (hP : ∀ g, g ∈ P.J ↔ g ∈ KO k ι ∧ ∀ a b, ¬ Fr a b → valuation k (g.val a b - (1 : Matrix ι ι k) a b) < 1)
    (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) :
    prX (Cgrp (P.map (typeFrame ϖ o).conj).J 1) = (P.map (typeFrame ϖ o).conj).J.comap (embX c) := by
  have key : ∀ g : GL n k, g ∈ prX (Cgrp (P.map (typeFrame ϖ o).conj).J 1) →
      IntM ((typeFrame ϖ o).conj.symm (embX c g)).val ∧ ∀ a b, ¬ Fr a b →
        valuation k (((typeFrame ϖ o).conj.symm (embX c g)).val a b - (1 : Matrix ι ι k) a b) < 1 := by
    rintro g ⟨u, hu, hg⟩
    have h := (mem_Cgrp.1 hg).2
    rw [inv_one, one_mul, mul_one, Level.mem_map, hP] at h
    refine ⟨fun a b => ?_, fun a b hab => ?_⟩
    · rcases entry_cases ϖ o (N_le_fixX hu) g a b with e | e <;> rw [e]
      · exact intM_of_mem_KO h.1 a b
      · exact intM_one a b
    · rcases entry_cases ϖ o (N_le_fixX hu) g a b with e | e <;> rw [e]
      · exact h.2 a b hab
      · simp
  ext g
  rw [Subgroup.mem_comap]
  refine ⟨fun hg => ?_, fun hg => ⟨1, one_mem _, mem_Cgrp.2 ⟨?_, by simpa using hg⟩⟩⟩
  · rw [Level.mem_map, hP]
    refine ⟨mem_KO.2 ⟨(key g hg).1, ?_⟩, (key g hg).2⟩
    rw [← map_inv, ← map_inv]
    exact (key g⁻¹ (inv_mem hg)).1
  · rw [one_mul]
    exact Subgroup.mem_sup_left ⟨g, rfl⟩

theorem prLevel_of_pattern (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (h : S.Pattern t) : S.PrLevel t :=
  fun j c H => prX_eq_comap (S.P.iter t S.μ S.tame j).toLevel (FreeIx S.ρ) (h j) S.ϖ (stdOrd (Fin κ) t j c H)

end GlobalTheory.SymChain.PrImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToOneSpherical
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

namespace GlobalTheory.PosOneSpherical

theorem toOne_spherical : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : HasConductor ψ 1) (ν : Measure k) (_ : IsUnitVol ν) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (_ : IsNEquiv ψ P σ l) (v : A), (∀ g ∈ KO k (n ⊕ Fin c), σ g v = v) → toOne ν σ P l v = l v := by
  intro k _ _ _ _ _ _ n _ _ c P hP hPc ψ hψc hcond ν hν A _ _ σ hσ l hl v hK
  have hne : ψ ≠ 1 := hcond.ne_one
  have hsd : IsSelfDual ψ ν := ((selfDual_measure k ψ hψc hne).2.1 hcond ν).1 hν
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨m, rfl⟩ : ∃ m, P = m + 1 := ⟨P - 1, by omega⟩
  have key : ∀ m : ℕ, m + 1 ≤ c → ∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ (m + 1) σ l →
      (Nat.rec (motive := fun _ => (A → ℂ) → A → ℂ) (fun l => l)
        (fun p rec l => rec (exDown ν (p + 1) σ l)) m : (A → ℂ) → A → ℂ) l v = l v := by
    intro m
    induction m with
    | zero => intro _ l _; rfl
    | succ m ih =>
      intro hm l hl
      have hlt : m + 1 < c := by omega
      obtain ⟨l', hl'v, hl'⟩ := (GlobalTheory.RootEx.Exchange.exchange_isPos k n c (m + 1) (by omega) hlt ψ hψc hne ν A σ hσ).2.1 l hl
      have hfun : exDown ν (m + 1) σ l = l' := funext fun w => (hl'v w).symm
      show (Nat.rec (motive := fun _ => (A → ℂ) → A → ℂ) (fun l => l)
        (fun p rec l => rec (exDown ν (p + 1) σ l)) m : (A → ℂ) → A → ℂ) (exDown ν (m + 1) σ l) v = l v
      rw [hfun, ih (by omega) l' hl']
      have h1 := (exDown_exUp_and_exUp_exDown k n c (m + 1) (by omega) hlt ψ hψc hne ν hsd A σ hσ l v).2 hl
      rw [hfun] at h1
      have h2 := (GlobalTheory.RootExchangeFixed.exUp_fixed_vector k n c (m + 1) (by omega) hlt ψ hcond ν hν A σ l' hl' v).2 hK
      rw [← h2, h1]
  exact key m hPc l hl

end GlobalTheory.PosOneSpherical
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpZeroMemLev
section
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.LevZeroGen
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

def xZero (κ t : Type) : κ ≃ XIx κ t 0 := (Equiv.sumEmpty κ (Fin 0)).symm.trans (Equiv.sumEmpty (κ ⊕ Fin 0) (Fin 0 × t)).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

def upZero : GL (Fin κ ⊕ Fin (s + 1)) k ≃* GL (XIx (Fin κ) t 0 ⊕ Fin (s + 1)) k :=
  (reGL (ixZero (Fin κ ⊕ Fin (s + 1)) t)).trans (typeFrame S.ϖ (stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _))).conj

theorem upZero_apply (x : GL (Fin κ ⊕ Fin (s + 1)) k) : upZero S t x =
    (S.T t).bas 0 (s + 1) (Nat.zero_add _) *
      reGL (stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _)) (reGL (ixZero (Fin κ ⊕ Fin (s + 1)) t) x) *
      ((S.T t).bas 0 (s + 1) (Nat.zero_add _))⁻¹ := rfl


open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {s κ : ℕ} (S : _root_.GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] in
theorem _root_.GlobalTheory.LevZeroGen.upZero_mem_lev (x : GL (Fin κ ⊕ Fin (s + 1)) k) :
    _root_.GlobalTheory.LevZeroGen.upZero S t x ∈
        ((S.T t).lev 0 (s + 1)
          (Nat.zero_add _)).J ↔
      x ∈ S.P.J := by
  show _ ∈ (_root_.GlobalTheory.StepData.Level.map _ _).J ↔ _
  rw [_root_.GlobalTheory.StepData.Level.mem_map, _root_.GlobalTheory.LevZeroGen.upZero,
    MulEquiv.trans_apply]
  erw [MulEquiv.symm_apply_apply]
  rw [_root_.GlobalTheory.StepData.TypeDatum.iter_zero]
  unfold _root_.GlobalTheory.StepData.TypeDatum.reindex
  show _ ∈ (_root_.GlobalTheory.StepData.Level.map _ _).J ↔ _
  rw [_root_.GlobalTheory.StepData.Level.mem_map, MulEquiv.symm_apply_apply]

end GlobalTheory.LevZeroGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntBiInvariant
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ZonalBi

theorem zonalInt_biInvariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ ψ : GL (Fin N) k → ℂ, (∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g) → ∀ κ ∈ KO k (Fin N), ∀ m, zonalInt μK ψ (κ * m) = zonalInt μK ψ m ∧ zonalInt μK ψ (m * κ) = zonalInt μK ψ m := by
  intro k _ _ _ _ N _ _ μK _ hK ψ hψ κ₀ hκ₀ m
  have hKo : IsOpen (KO k (Fin N) : Set (GL (Fin N) k)) := GlobalTheory.SplitFlip.isOpen_KO
  have hKc : IsCompact (KO k (Fin N) : Set (GL (Fin N) k)) := GlobalTheory.SplitFlip.isCompact_KO
  have hKcl : IsClosed (KO k (Fin N) : Set (GL (Fin N) k)) := Subgroup.isClosed_of_isOpen _ hKo
  have hKfr : frontier (KO k (Fin N) : Set (GL (Fin N) k)) = ∅ := (IsClopen.frontier_eq ⟨hKcl, hKo⟩)
  have hKm : MeasurableSet (KO k (Fin N) : Set (GL (Fin N) k)) := hKo.measurableSet
  have hψc : Continuous ψ := by
    refine continuous_iff_continuousAt.2 fun g => ?_
    have hmem : (fun y => g⁻¹ * y) ⁻¹' (KO k (Fin N) : Set (GL (Fin N) k)) ∈ nhds g :=
      (hKo.preimage (continuous_const_mul g⁻¹)).mem_nhds (by simp [one_mem])
    have hev : ∀ᶠ y in nhds g, ψ y = ψ g := by
      filter_upwards [hmem] with y hy
      have := hψ g (g⁻¹ * y) hy
      rwa [mul_inv_cancel_left] at this
    exact tendsto_nhds_of_eventually_eq hev
  refine ⟨?_, ?_⟩
  · set ν : Measure (GL (Fin N) k) := Measure.map (· * κ₀) μK with hν
    set c := Measure.haarScalarFactor ν μK with hc
    have L : ∀ f : GL (Fin N) k → ℝ, Continuous f → HasCompactSupport f →
        ∫ x, f x ∂ν = ∫ x, f x ∂(c • μK) := fun f hf hs =>
      Measure.integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport ν μK hf hs
    have hpre : (· * κ₀) ⁻¹' (KO k (Fin N) : Set (GL (Fin N) k)) = KO k (Fin N) := by
      ext x; simp [Subgroup.mul_mem_cancel_right _ hκ₀]
    have hc1 : c = 1 := by
      have h1 := L ((KO k (Fin N) : Set (GL (Fin N) k)).indicator 1)
        (continuous_indicator (by simp [hKfr]) continuous_one.continuousOn)
        (HasCompactSupport.intro hKc fun x hx => by simp [hx])
      rw [integral_indicator_one hKm, integral_indicator_one hKm] at h1
      simp only [Measure.real, hν, Measure.map_apply (measurable_mul_const κ₀) hKm, hpre, Measure.smul_apply, hK] at h1
      simpa using h1.symm
    set F : GL (Fin N) k → ℂ := (KO k (Fin N) : Set (GL (Fin N) k)).indicator fun x => ψ (x * m) with hFdef
    have hF : Continuous F :=
      continuous_indicator (by simp [hKfr]) (hψc.comp (continuous_mul_const m)).continuousOn
    have hFs : HasCompactSupport F := HasCompactSupport.intro hKc fun x hx => by simp [F, hx]
    have e1 : zonalInt μK ψ (κ₀ * m) = ∫ x, F (x * κ₀) ∂μK := by
      unfold zonalInt
      rw [← integral_indicator hKm]
      congr 1; funext x
      by_cases hx : x ∈ KO k (Fin N)
      · have hx' : x * κ₀ ∈ KO k (Fin N) := mul_mem hx hκ₀
        rw [hFdef, Set.indicator_of_mem (SetLike.mem_coe.2 hx), Set.indicator_of_mem (SetLike.mem_coe.2 hx'), mul_assoc]
      · have hx' : x * κ₀ ∉ KO k (Fin N) := fun h => hx ((Subgroup.mul_mem_cancel_right _ hκ₀).1 h)
        rw [hFdef, Set.indicator_of_notMem (fun h => hx (SetLike.mem_coe.1 h)),
          Set.indicator_of_notMem (fun h => hx' (SetLike.mem_coe.1 h))]
    have e2 : zonalInt μK ψ m = ∫ x, F x ∂μK := by
      unfold zonalInt; rw [← integral_indicator hKm]
    have e3 : ∫ x, F (x * κ₀) ∂μK = ∫ x, F x ∂ν :=
      (integral_map (measurable_mul_const κ₀).aemeasurable hF.aestronglyMeasurable).symm
    have hIν : Integrable F ν := hF.integrable_of_hasCompactSupport hFs
    have hIμ : Integrable F μK := hF.integrable_of_hasCompactSupport hFs
    have Lre := L (fun x => (F x).re) (Complex.continuous_re.comp hF) (hFs.comp_left Complex.zero_re)
    have Lim := L (fun x => (F x).im) (Complex.continuous_im.comp hF) (hFs.comp_left Complex.zero_im)
    rw [hc1, one_smul] at Lre Lim
    have e4 : ∫ x, F x ∂ν = ∫ x, F x ∂μK := by
      apply Complex.ext
      · have a := integral_re hIν
        have b := integral_re hIμ
        simp only [RCLike.re_to_complex] at a b
        rw [← a, ← b, Lre]
      · have a := integral_im hIν
        have b := integral_im hIμ
        simp only [RCLike.im_to_complex] at a b
        rw [← a, ← b, Lim]
    rw [e1, e3, e4, e2]
  · unfold zonalInt
    congr 1; funext κ
    rw [← mul_assoc, hψ _ _ hκ₀]

end GlobalTheory.ZonalBi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntEig
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ZonalEig

theorem zonalInt_eig : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ ψ : GL (Fin N) k → ℂ, (∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g) → ∀ (R : Finset (GL (Fin N) k)) (c : ℂ), (∀ m, ∑ g ∈ R, ψ (m * g) = c * ψ m) → ∀ m, ∑ g ∈ R, zonalInt μK ψ (m * g) = c * zonalInt μK ψ m := by
  intro k _ _ _ _ N _ _ μK _ hμ ψ hψ R c hR m
  have hKo := (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := Fin N))
  have hcont : Continuous ψ := by
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_)
    have ho : IsOpen ((fun x => g⁻¹ * x) ⁻¹' (KO k (Fin N) : Set (GL (Fin N) k))) := hKo.preimage (by fun_prop)
    filter_upwards [ho.mem_nhds (show g⁻¹ * g ∈ (KO k (Fin N) : Set (GL (Fin N) k)) by
      rw [inv_mul_cancel]; exact one_mem _)] with x hx
    have := hψ g _ hx
    rwa [mul_inv_cancel_left] at this
  have hint : ∀ y, IntegrableOn (fun κ => ψ (κ * y)) (KO k (Fin N) : Set (GL (Fin N) k)) μK := fun y =>
    (hcont.comp (continuous_mul_const y)).continuousOn.integrableOn_compact GlobalTheory.SplitFlip.isCompact_KO
  simp only [zonalInt]
  rw [← integral_finsetSum _ (fun g _ => hint (m * g)), ← integral_const_mul]
  congr 1
  funext κ
  have := hR (κ * m)
  simpa only [mul_assoc] using this

end GlobalTheory.ZonalEig
end
end

