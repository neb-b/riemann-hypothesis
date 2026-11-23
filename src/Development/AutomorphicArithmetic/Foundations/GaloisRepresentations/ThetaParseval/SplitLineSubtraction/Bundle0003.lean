module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSSLeft
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

section
open scoped Matrix

variable {Γ k : Type} [Group Γ] [Field k]

private def inc (a b : ℕ) : (Fin a → k) →ₗ[k] (Fin (a + b) → k) where
  toFun x := Sum.elim x 0 ∘ finSumFinEquiv.symm
  map_add' x y := by
    funext i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    cases j <;> simp
  map_smul' c x := by
    funext i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    cases j <;> simp

private theorem inc_inl {a b : ℕ} (x : Fin a → k) (i : Fin a) :
    inc a b x (finSumFinEquiv (Sum.inl i)) = x i := by
  simp [inc]

private theorem inc_inr {a b : ℕ} (x : Fin a → k) (j : Fin b) :
    inc a b x (finSumFinEquiv (Sum.inr j)) = 0 := by
  simp [inc]

private theorem inc_injective {a b : ℕ} : Function.Injective (inc (k := k) a b) := by
  intro x y h
  funext i
  rw [← inc_inl (b := b) x i, ← inc_inl (b := b) y i, h]

private theorem sum_mulVec_inc {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k) (g : Γ)
    (x : Fin a → k) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) *ᵥ inc a b x =
      inc a b ((r g : Matrix (Fin a) (Fin a) k) *ᵥ x) := by
  funext i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  rcases j with j | j
  · rw [GlobalTheory.EigTwist.sumRep_mulVec_inl, inc_inl]
    congr 1
    funext i
    exact inc_inl x i
  · rw [GlobalTheory.EigTwist.sumRep_mulVec_inr, inc_inr]
    have : (inc a b x ∘ finSumFinEquiv ∘ Sum.inr : Fin b → k) = 0 := by
      funext i
      exact inc_inr x i
    rw [this, Matrix.mulVec_zero]
    rfl

private theorem ss_left {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k)
    (h : IsSSRep (sumRep r s)) : IsSSRep r := by
  intro W hW
  obtain ⟨C, hC, hc⟩ := h (W.map (inc a b)) (by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨_, hW g x hx, (sum_mulVec_inc r s g x).symm⟩)
  refine ⟨C.comap (inc a b), fun g v hv => ?_, ?_, ?_⟩
  · show inc a b _ ∈ C
    rw [← sum_mulVec_inc r s g v]
    exact hC g _ hv
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    have h0 : inc a b x ∈ W.map (inc a b) ⊓ C := ⟨⟨x, hx, rfl⟩, hx'⟩
    rw [hc.disjoint.eq_bot, Submodule.mem_bot] at h0
    exact inc_injective (h0.trans (map_zero _).symm)
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : inc a b x ∈ W.map (inc a b) ⊔ C := by
      rw [hc.codisjoint.eq_top]
      exact Submodule.mem_top
    obtain ⟨_, ⟨w, hw, rfl⟩, z, hz, hzx⟩ := Submodule.mem_sup.1 hx
    have hz' : z = inc a b (x - w) := by
      rw [map_sub, ← hzx]
      abel
    refine Submodule.mem_sup.2 ⟨w, hw, x - w, ?_, by abel⟩
    show inc a b (x - w) ∈ C
    rwa [← hz']

private theorem ss_of_iso {n : ℕ} (r r' : Γ →* GL (Fin n) k) (h : RepIso r r') (hr : IsSSRep r) :
    IsSSRep r' := by
  obtain ⟨g, hg⟩ := h
  let e : (Fin n → k) ≃ₗ[k] (Fin n → k) := Matrix.toLin'OfInv
    (M := ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (M' := (g : Matrix (Fin n) (Fin n) k))
    (Units.inv_mul g) (Units.mul_inv g)
  have he : ∀ v, e v = (g : Matrix (Fin n) (Fin n) k) *ᵥ v := fun v => rfl
  have key : ∀ s v, e ((r s : Matrix (Fin n) (Fin n) k) *ᵥ v) = (r' s : Matrix (Fin n) (Fin n) k) *ᵥ e v := by
    intro s v
    rw [he, he, hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      inv_mul_cancel_right]
  intro W hW
  obtain ⟨C, hC, hc⟩ := hr (W.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))) (by
    intro s v hv
    show e _ ∈ W
    rw [key]
    exact hW s _ hv)
  refine ⟨C.map (e : (Fin n → k) →ₗ[k] (Fin n → k)), ?_, ?_⟩
  · rintro s _ ⟨u, hu, rfl⟩
    exact ⟨_, hC s u hu, key s u⟩
  · have h2 : IsCompl ((W.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))).map (e : (Fin n → k) →ₗ[k] (Fin n → k)))
        (C.map (e : (Fin n → k) →ₗ[k] (Fin n → k))) := (Submodule.orderIsoMapComap e).isCompl hc
    rwa [Submodule.map_comap_eq_of_surjective e.surjective] at h2

private theorem ss_tw {n : ℕ} (r : Γ →* GL (Fin n) k) (c : Γ →* kˣ) (hr : IsSSRep r) :
    IsSSRep (tw r c) := by
  intro W hW
  have hW' : IsInv r W := by
    intro g v hv
    have h1 := W.smul_mem ((c g)⁻¹ : kˣ).val (hW g v hv)
    rw [UpperTheory.V.Af.tw_val, Matrix.smul_mulVec, smul_smul, Units.val_inv_eq_inv_val,
      inv_mul_cancel₀ (c g).ne_zero, one_smul] at h1
    exact h1
  obtain ⟨C, hC, hc⟩ := hr W hW'
  refine ⟨C, fun g v hv => ?_, hc⟩
  rw [UpperTheory.V.Af.tw_val, Matrix.smul_mulVec]
  exact C.smul_mem _ (hC g v hv)

end

theorem UpperTheory.Gal.TP.Sub.sSLeft_holds :
    SSLeft := by
  intro Γ k _ _ a b
  exact ⟨fun r s h => ss_left r s h, fun r r' h hr => ss_of_iso r r' h hr, fun r c h => ss_tw r c h⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSplitLine
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

noncomputable section

namespace UpperTheory.Gal.TP.Sub

section SplitLineAux

variable {Γ k : Type} [Group Γ] [Field k] {m : ℕ}

private lemma sumRep_val (s : Γ →* GL (Fin m) k) (c : Γ →* kˣ) (g : Γ) :
    ((sumRep s (rk1 c) g : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      (Matrix.fromBlocks (s g : Matrix (Fin m) (Fin m) k) 0 0
        ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := rfl

private lemma rankOneRep_val (c : Γ →* kˣ) (g : Γ) (i j : Fin 1) :
    ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k) i j = (c g : k) := by
  simp [rk1, Subsingleton.elim i j]

private def resHom (r : Γ →* GL (Fin (m + 1)) k) {W' : Submodule k (Fin (m + 1) → k)}
    (hinv : IsInv r W') : Γ →* Module.End k W' where
  toFun g := (Matrix.mulVecLin (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)).restrict (hinv g)
  map_one' := by ext x; simp
  map_mul' g h := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change (r (g * h) : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (x : Fin (m + 1) → k) =
      (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec
        ((r h : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (x : Fin (m + 1) → k))
    simp [Matrix.mulVec_mulVec]

private def subRep (r : Γ →* GL (Fin (m + 1)) k) {W' : Submodule k (Fin (m + 1) → k)}
    (hinv : IsInv r W') (b : Module.Basis (Fin m) k W') : Γ →* GL (Fin m) k :=
  MonoidHom.toHomUnits
    { toFun := fun g => LinearMap.toMatrix b b (resHom r hinv g)
      map_one' := by simp [LinearMap.toMatrix_one]
      map_mul' := fun g h => by
        rw [map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix_comp b b b] }

private lemma subRep_val (r : Γ →* GL (Fin (m + 1)) k) {W' : Submodule k (Fin (m + 1) → k)}
    (hinv : IsInv r W') (b : Module.Basis (Fin m) k W') (g : Γ) :
    ((subRep r hinv b g : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) =
      LinearMap.toMatrix b b (resHom r hinv g) := rfl

private def colM {W' : Submodule k (Fin (m + 1) → k)} (b : Module.Basis (Fin m) k W')
    (v : Fin (m + 1) → k) : Matrix (Fin (m + 1)) (Fin m ⊕ Fin 1) k :=
  Matrix.of fun i => Sum.elim (fun j => (b j : Fin (m + 1) → k) i) (fun _ => v i)

private lemma intertw (r : Γ →* GL (Fin (m + 1)) k) {W' : Submodule k (Fin (m + 1) → k)}
    (hinv : IsInv r W') (b : Module.Basis (Fin m) k W') (c : Γ →* kˣ) (v : Fin (m + 1) → k)
    (hv : ∀ g, (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec v = (c g : k) • v) (g : Γ) :
    (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * colM b v =
      colM b v * Matrix.fromBlocks (subRep r hinv b g : Matrix (Fin m) (Fin m) k) 0 0
        ((rk1 c g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k) := by
  ext i j
  rcases j with j | j
  · have h1 : ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * colM b v) i (Sum.inl j) =
        ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (b j : Fin (m + 1) → k)) i := rfl
    have h2 := b.sum_repr (resHom r hinv g (b j))
    have h4 : ((resHom r hinv g (b j) : W') : Fin (m + 1) → k) =
        (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (b j : Fin (m + 1) → k) := rfl
    have h3 : ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (b j : Fin (m + 1) → k)) i =
        ∑ a, (b.repr (resHom r hinv g (b j))) a * (b a : Fin (m + 1) → k) i := by
      have h5 := congrArg (fun u : W' => (u : Fin (m + 1) → k) i) h2
      simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul] at h5
      rw [← h4, h5]
    rw [h1, h3, Matrix.mul_apply, Fintype.sum_sum_type]
    simp [subRep_val, colM, LinearMap.toMatrix_apply, mul_comm]
  · have h1 : ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * colM b v) i (Sum.inr j) =
        ((r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec v) i := rfl
    rw [h1, hv g, Matrix.mul_apply, Fintype.sum_sum_type]
    simp [colM, rankOneRep_val, mul_comm]

private lemma col_indep {W' : Submodule k (Fin (m + 1) → k)} (b : Module.Basis (Fin m) k W')
    {v : Fin (m + 1) → k} (hv0 : v ≠ 0) (hc : IsCompl (Submodule.span k {v}) W') :
    LinearIndependent k (Sum.elim (fun j => (b j : Fin (m + 1) → k)) (fun _ : Fin 1 => v)) := by
  refine LinearIndependent.sum_type
    (b.linearIndependent.map' W'.subtype (Submodule.ker_subtype W'))
    (LinearIndependent.of_subsingleton (0 : Fin 1) hv0) ?_
  refine Disjoint.mono ?_ ?_ hc.disjoint.symm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (b j).2
  · rw [Set.range_const]

end SplitLineAux

end UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.splitLine_holds : SplitLine := by
  intro Γ k _ _ m r hss c ⟨v, hv0, hv⟩
  have hW : IsInv r (Submodule.span k {v}) := by
    intro g x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [Matrix.mulVec_smul, hv g, smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  obtain ⟨W', hinv, hc⟩ := hss _ hW
  have hfr : Module.finrank k W' = m := by
    have h := Submodule.finrank_add_eq_of_isCompl hc
    rw [finrank_span_singleton hv0, Module.finrank_fin_fun] at h
    omega
  let b : Module.Basis (Fin m) k W' := Module.finBasisOfFinrankEq k W' hfr
  let Q : Matrix (Fin (m + 1)) (Fin (m + 1)) k := (colM b v).submatrix id finSumFinEquiv.symm
  have hQ : IsUnit Q := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have := (col_indep b hv0 hc).comp finSumFinEquiv.symm finSumFinEquiv.symm.injective
    convert this using 1
    ext j i
    rcases h : finSumFinEquiv.symm j with j' | j' <;> simp [Q, colM, Matrix.col, h]
  obtain ⟨q, hq⟩ := hQ
  refine ⟨subRep r hinv b, q⁻¹, fun g => ?_⟩
  have key : (r g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * Q =
      Q * (sumRep (subRep r hinv b) (rk1 c) g : GL (Fin (m + 1)) k) := by
    rw [sumRep_val]
    change _ * (colM b v).submatrix id finSumFinEquiv.symm =
      (colM b v).submatrix id finSumFinEquiv.symm * _
    rw [Matrix.submatrix_mul_equiv, ← intertw r hinv b c v hv g]
    ext i j
    rfl
  have key2 : r g * q = q * sumRep (subRep r hinv b) (rk1 c) g := Units.ext (by
    simpa [hq] using key)
  rw [inv_inv, mul_assoc, key2, ← mul_assoc, inv_mul_cancel, one_mul]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSumDR
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.TP.Sub

section Alg

variable {Γ : Type} [Group Γ] {k k' : Type} [CommRing k] [CommRing k']

private theorem sumRep_ll {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k) (g : Γ) (i j : Fin a) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j) =
      (r g : Matrix (Fin a) (Fin a) k) i j := by
  change Matrix.fromBlocks (r g : Matrix (Fin a) (Fin a) k) 0 0 (s g : Matrix (Fin b) (Fin b) k)
      (finSumFinEquiv.symm (Fin.castAdd b i)) (finSumFinEquiv.symm (Fin.castAdd b j)) = _
  simp

private theorem sumRep_rr {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k) (g : Γ) (i j : Fin b) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.natAdd a i) (Fin.natAdd a j) =
      (s g : Matrix (Fin b) (Fin b) k) i j := by
  change Matrix.fromBlocks (r g : Matrix (Fin a) (Fin a) k) 0 0 (s g : Matrix (Fin b) (Fin b) k)
      (finSumFinEquiv.symm (Fin.natAdd a i)) (finSumFinEquiv.symm (Fin.natAdd a j)) = _
  simp

private theorem map_sum' {a b : ℕ} (f : k →+* k') (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k) :
    mapRep f (sumRep r₁ r₂) = sumRep (mapRep f r₁) (mapRep f r₂) := by
  ext g i j
  change f (Matrix.fromBlocks (r₁ g : Matrix (Fin a) (Fin a) k) 0 0 (r₂ g : Matrix (Fin b) (Fin b) k)
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) =
    Matrix.fromBlocks (mapRep f r₁ g : Matrix (Fin a) (Fin a) k') 0 0 (mapRep f r₂ g : Matrix (Fin b) (Fin b) k')
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [mapRep]

private theorem descend {n : ℕ} (f : k →+* k') (hf : Function.Injective f) (r : Γ →* GL (Fin n) k')
    (A : Γ → Matrix (Fin n) (Fin n) k) (hA : ∀ g i j, f (A g i j) = (r g : Matrix (Fin n) (Fin n) k') i j) :
    ∃ r₁ : Γ →* GL (Fin n) k, mapRep f r₁ = r := by
  let M : Γ →* Matrix (Fin n) (Fin n) k :=
    { toFun := A
      map_one' := by
        ext i j
        apply hf
        rw [hA]
        simp [Matrix.one_apply, apply_ite f]
      map_mul' := fun g h => by
        ext i j
        apply hf
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hA, Matrix.mul_apply, map_sum]
        simp only [map_mul, hA, Units.val_mul, Matrix.mul_apply] }
  refine ⟨M.toHomUnits, ?_⟩
  ext g i j
  simpa [mapRep, M] using hA g i j

end Alg

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {Bw : LocBridge l E Ω Gw O} {a b : ℕ}
  {r : ↥Gw →* GL (Fin a) (Om l)} {s : ↥Gw →* GL (Fin b) (Om l)}

private theorem model_split {L : FinExt l} {ρ : ↥Gw →* GL (Fin (a + b)) ↥L.1}
    (h : IsModel Bw (sumRep r s) L ρ) :
    ∃ (r₁ : ↥Gw →* GL (Fin a) ↥L.1) (s₁ : ↥Gw →* GL (Fin b) ↥L.1),
      IsModel Bw r L r₁ ∧ IsModel Bw s L s₁ ∧ IsModel Bw (sumRep r s) L (sumRep r₁ s₁) := by
  have hf : Function.Injective (algebraMap ↥L.1 (Om l)) := (algebraMap ↥L.1 (Om l)).injective
  have e : ∀ g i j, algebraMap ↥L.1 (Om l) ((ρ g : Matrix _ _ ↥L.1) i j) =
      (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) (Om l)) i j := fun g i j => by
    rw [← h.2]
    simp [mapRep]
  obtain ⟨r₁, hr⟩ := descend (algebraMap ↥L.1 (Om l)) hf r
    (fun g i j => (ρ g : Matrix _ _ ↥L.1) (Fin.castAdd b i) (Fin.castAdd b j))
    (fun g i j => by rw [e, sumRep_ll])
  obtain ⟨s₁, hs⟩ := descend (algebraMap ↥L.1 (Om l)) hf s
    (fun g i j => (ρ g : Matrix _ _ ↥L.1) (Fin.natAdd a i) (Fin.natAdd a j))
    (fun g i j => by rw [e, sumRep_rr])
  exact ⟨r₁, s₁, ⟨h.1, hr⟩, ⟨h.1, hs⟩, ⟨h.1, by rw [map_sum', hr, hs]⟩⟩

theorem sumDR_holds : SumDR := by
  intro l _ P AI tied E Ω _ _ _ _ _ A O _ _ _ Bw a b r s hd
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨L, ρ, hm, -⟩ := id hd
    obtain ⟨r₁, s₁, m₁, m₂, m⟩ := model_split hm
    have S := _root_.GlobalTheory.DirectSumLocal.isdRE_sumRep_and_multE_add l P AI tied E Ω _ O Bw L a b r₁ s₁
    exact ⟨L, r₁, m₁, (S.1.1 ((m.isdRAt_iff P).1 hd)).1⟩
  · obtain ⟨L, ρ, hm, -⟩ := id hd
    obtain ⟨r₁, s₁, m₁, m₂, m⟩ := model_split hm
    have S := _root_.GlobalTheory.DirectSumLocal.isdRE_sumRep_and_multE_add l P AI tied E Ω _ O Bw L a b r₁ s₁
    exact ⟨L, s₁, m₂, (S.1.1 ((m.isdRAt_iff P).1 hd)).2⟩
  · intro τ J J' hJ hJ'
    obtain ⟨L, ρ, hm, -, τ', t, -⟩ := id hJ
    obtain ⟨r₁, s₁, m₁, m₂, m⟩ := model_split hm
    have S := _root_.GlobalTheory.DirectSumLocal.isdRE_sumRep_and_multE_add l P AI tied E Ω _ O Bw L a b r₁ s₁
    refine ⟨L, r₁, m₁, (S.1.1 ((m.isdRAt_iff P).1 hd)).1, τ', t, fun n => ?_⟩
    have c₁ := hJ.count_eq P m t n
    have c₂ := hJ'.count_eq P m₂ t n
    rw [S.2, Multiset.count_add, Nat.cast_add, c₂] at c₁
    linarith

end UpperTheory.Gal.TP.Sub

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PTwJumps
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw tw_val)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.TP.Sub

theorem twJumps_holds : TwJumps := by
  intro l _ P AI hT E Ω _ _ _ _ _ A O _ _ _ Bw a r c _ _ τ J m h1 h2
  exact (GlobalTheory.TwistAbove.twist_above l P AI hT E Ω (Dec (F := E) A) O Bw a r (tw r c) c
    (fun g => tw_val r c g)).2.2.2 τ J m h1 h2

end UpperTheory.Gal.TP.Sub

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PTwLoc
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.twLoc_holds :
    TwLoc := by
  intro l _ P AI hT E Ω _ _ _ _ _ A O _ _ _ Bw a r c
  have h := GlobalTheory.TwistAbove.twist_above l P AI hT E Ω (Dec (F := E) A) O Bw a r (tw r c) c
    (fun g => UpperTheory.V.Af.tw_val r c g)
  exact ⟨h.1, h.2.1⟩
end

