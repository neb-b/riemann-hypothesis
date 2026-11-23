module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0323
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeOrthogonalSumLineAtSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LineSplitAt
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

theorem mulVec_sec {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (u : Fin n → k) :
    M *ᵥ (fun i => p.sec (u i)) = fun i => p.sec ((M.map p.pr *ᵥ u) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, FrameLat.sec_mul_right, mul_comm (u j)]

theorem mulVec_csec {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (z : Fin n → k) :
    M *ᵥ (fun i => cA D (p.sec (z i))) = fun i => cA D (p.sec ((M.map (fun a => p.pr (cA D a)) *ᵥ z) i)) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [FrameLat.sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, FrameLat.e_mul_sec, map_mul, cA_cA]

theorem eq_sec_add_csec {n : ℕ} {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D (· = p.v)) :
    y = (fun i => p.sec (p.pr (y i))) + (fun i => cA D (p.sec (p.pr (cA D (y i))))) := by
  funext i
  have h := (FrameLat.idem_iff p (y i)).1 (hy i)
  simp only [Pi.add_apply, p.sec_pr, map_mul, cA_cA]
  rw [← add_mul, h]

variable {p}

theorem mulVec_mem_of_parts {S T : HSp D} {L : Lat S} {L' : Lat T} (hL : IsSelfDualC S L)
    (M : Matrix (Fin T.rank) (Fin S.rank) (AE D))
    (hw : ∀ u, (fun i => p.sec (u i)) ∈ latV S L (· = p.v) → (fun i => p.sec ((M.map p.pr *ᵥ u) i)) ∈ latV T L' (· = p.v))
    (hc : ∀ z, (fun i => cA D (p.sec (z i))) ∈ latV S L (· = p.v) →
      (fun i => cA D (p.sec ((M.map (fun a => p.pr (cA D a)) *ᵥ z) i))) ∈ latV T L' (· = p.v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = p.v)) : M *ᵥ y ∈ latV T L' (· = p.v) := by
  have e := eq_sec_add_csec p (FrameLat.latV_supp hy)
  rw [e] at hy ⊢
  have h := (FrameLat.decomp hL _ _).1 hy
  rw [Matrix.mulVec_add, mulVec_sec, mulVec_csec]
  exact add_mem (hw _ h.1) (hc _ h.2)

theorem pair_eq (S : HSp D) (x z : Fin S.rank → k) :
    ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * z j =
      x ⬝ᵥ (S.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, RingHom.comp_apply, mul_assoc]

theorem conjT_map {m n : Type} (M : Matrix m n D.host.E) :
    Mᴴ.map (p.pr.comp ((cA D).comp (incA D))) = (M.map (p.pr.comp (incA D)))ᵀ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, RingHom.comp_apply, FrameLat.cA_incA,
    star_star]

end GlobalTheory.LineSplitAt

namespace GlobalTheory.LineSplitAt


set_option maxHeartbeats 1000000 in
theorem orthAt_of_frames : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n' : Type) [Fintype n'] [DecidableEq n'] (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → p.UnitAA → ∀ (LA : Lat A) (LS : Lat S) (ΛA : Submodule 𝒪[k] (n' → k)), IsSelfDualC A LA → IsSelfDualC S LS → α.IsLat LA ΛA → α₀.IsLat LS (lastKer ΛA) → ∃ LL : Lat L, OrthAt o LS LA LL p.v := by
  intro D k _ _ _ _ p n' _ _ S A L o ζ _ α α₀ hsum _ LA LS ΛA hLA hLS hα hα₀
  have hb : α₀.b = fromCols (o.jA.map p.pr * α.b) (replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i)) := hsum
  have hPJ : o.pA.map p.pr * o.jA.map p.pr = 1 := by
    rw [← Matrix.map_mul, o.pA_jA, Matrix.map_one _ (map_zero _) (map_one _)]
  have hz : o.pA.map p.pr *ᵥ (⇑p.pr ∘ ratV (vecB o ζ)) = 0 := by
    have e1 : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
      funext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [ratV, vecB, OrthDec.jB, rat, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    funext i
    rw [← RingHom.map_mulVec, e1, Matrix.mulVec_mulVec, o.pA_jB, Matrix.zero_mulVec]
    simp
  have hPz : o.pA.map p.pr * replicateCol (Fin 1) (fun i => p.pr (ratV (vecB o ζ) i)) = 0 := by
    ext i j
    have := congrFun hz i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

  have hwA : ∀ u : Fin A.rank → k, (fun i => p.sec (u i)) ∈ latV A LA (· = p.v) →
      (fun i => p.sec ((o.jA.map p.pr *ᵥ u) i)) ∈ latV S LS (· = p.v) := by
    intro u hu
    have hx : α.b' *ᵥ u ∈ ΛA := (hα _).2 (by rwa [Matrix.mulVec_mulVec, α.bb', Matrix.one_mulVec])
    have e : o.jA.map p.pr *ᵥ u = α₀.b *ᵥ Sum.elim (α.b' *ᵥ u) 0 := by
      rw [hb, Matrix.fromCols_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_mulVec, Matrix.mul_assoc, α.bb',
        Matrix.mul_one, Matrix.mulVec_zero, add_zero]
    rw [e]
    exact (hα₀ _).1 (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨by simpa using hx, by simp⟩)
  have hwS : ∀ u : Fin S.rank → k, (fun i => p.sec (u i)) ∈ latV S LS (· = p.v) →
      (fun i => p.sec ((o.pA.map p.pr *ᵥ u) i)) ∈ latV A LA (· = p.v) := by
    intro u hu
    have hy : α₀.b' *ᵥ u ∈ lastKer ΛA := (hα₀ _).2 (by rwa [Matrix.mulVec_mulVec, α₀.bb', Matrix.one_mulVec])
    have e : o.pA.map p.pr *ᵥ u = α.b *ᵥ ((α₀.b' *ᵥ u) ∘ Sum.inl) := by
      conv_lhs => rw [← Matrix.one_mulVec u, ← α₀.bb', ← Matrix.mulVec_mulVec, hb, Matrix.fromCols_mulVec, Matrix.mulVec_add,
        Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hPJ, Matrix.one_mul, Matrix.mulVec_mulVec _ (o.pA.map p.pr), hPz,
        Matrix.zero_mulVec, add_zero]
    rw [e]
    exact (hα _).1 (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy).1

  have hG2 : A.gram * o.qA = o.iAᴴ * S.gram := by
    rw [OrthDec.qA, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_isUnit_det A), Matrix.one_mul]
  have hG1 : S.gram * o.iA = o.qAᴴ * A.gram := by
    have := congrArg Matrix.conjTranspose hG2
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, gram_conjTranspose] at this
    exact this.symm
  have hcA : ∀ z : Fin A.rank → k, (fun i => cA D (p.sec (z i))) ∈ latV A LA (· = p.v) →
      (fun i => cA D (p.sec ((o.jA.map (fun a => p.pr (cA D a)) *ᵥ z) i))) ∈ latV S LS (· = p.v) := by
    intro z hz
    refine (FrameLat.csec_mem_iff hLS _).2 fun x hx => ?_
    have key : ∑ i, ∑ j, x i * p.pr (cA D (incA D (S.gram i j))) * (o.jA.map (fun a => p.pr (cA D a)) *ᵥ z) j =
        ∑ i, ∑ j, (o.pA.map p.pr *ᵥ x) i * p.pr (cA D (incA D (A.gram i j))) * z j := by
      rw [pair_eq, pair_eq]
      change x ⬝ᵥ (S.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ (o.iA.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z)) =
        (o.qA.map (p.pr.comp (incA D)) *ᵥ x) ⬝ᵥ (A.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z)
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hG1, Matrix.map_mul, conjT_map, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [key]
    exact (FrameLat.csec_mem_iff hLA z).1 hz _ (hwS x hx)
  have hcS : ∀ z : Fin S.rank → k, (fun i => cA D (p.sec (z i))) ∈ latV S LS (· = p.v) →
      (fun i => cA D (p.sec ((o.pA.map (fun a => p.pr (cA D a)) *ᵥ z) i))) ∈ latV A LA (· = p.v) := by
    intro z hz
    refine (FrameLat.csec_mem_iff hLA _).2 fun x hx => ?_
    have key : ∑ i, ∑ j, x i * p.pr (cA D (incA D (A.gram i j))) * (o.pA.map (fun a => p.pr (cA D a)) *ᵥ z) j =
        ∑ i, ∑ j, (o.jA.map p.pr *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) * z j := by
      rw [pair_eq, pair_eq]
      change x ⬝ᵥ (A.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ (o.qA.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z)) =
        (o.iA.map (p.pr.comp (incA D)) *ᵥ x) ⬝ᵥ (S.gram.map (p.pr.comp ((cA D).comp (incA D))) *ᵥ z)
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hG2, Matrix.map_mul, conjT_map, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [key]
    exact (FrameLat.csec_mem_iff hLS z).1 hz _ (hwA x hx)
  have h1 : ∀ y ∈ latV A LA (· = p.v), o.jA *ᵥ y ∈ latV S LS (· = p.v) := fun y hy =>
    mulVec_mem_of_parts hLA o.jA hwA hcA hy
  have h2 : ∀ y ∈ latV S LS (· = p.v), o.pA *ᵥ y ∈ latV A LA (· = p.v) := fun y hy =>
    mulVec_mem_of_parts hLS o.pA hwS hcS hy
  have hsplit : ∀ g : Fin S.rank → AE D, o.jA *ᵥ (o.pA *ᵥ g) + o.jB *ᵥ (o.pB *ᵥ g) = g := fun g => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.sum_eq_one, Matrix.one_mulVec]
  let fB := (mulVecLin o.qB).restrictScalars (𝓞 D.host.E)
  have h3 : ∀ x ∈ latV L (LS.map fB) (· = p.v), o.jB *ᵥ x ∈ latV S LS (· = p.v) := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, ha', c, hc, w, hw, rfl⟩ := hx
      rw [Set.mem_singleton_iff] at hc
      subst hc
      obtain ⟨s, hs, rfl⟩ := hw
      have hg : (fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * s i)) ∈ latV S LS (· = p.v) :=
        AddSubgroup.subset_closure ⟨a, ha, ha', 1, rfl, s, hs, rfl⟩
      have e2 : o.pB *ᵥ (fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * s i)) =
          fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * (o.qB *ᵥ s) i) := by
        funext i
        simp only [Matrix.mulVec, dotProduct, one_mul, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        change ((1 : AF D.host.F) ⊗ₜ[D.host.F] o.qB i j) * _ = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      show o.jB *ᵥ (fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * (o.qB *ᵥ s) i)) ∈ _
      rw [← e2]
      have hm := hg
      rw [← hsplit (fun i => pairA D.host.F 0 a ⊗ₜ[D.host.F] (1 * s i))] at hm
      exact (add_mem_cancel_left (h1 _ (h2 _ hg))).1 hm
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
    | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx
  refine ⟨LS.map fB, fun y => ⟨fun hy => ⟨h2 y hy, GlobalTheory.OrthSumLat.rat_mulVec_mem_latV o.qB
    (fun x hx => Submodule.mem_map_of_mem hx) hy⟩, fun h => ?_⟩⟩
  rw [← hsplit y]
  exact add_mem (h1 _ h.1) (h3 _ h.2)

end GlobalTheory.LineSplitAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalLevelZeroStabilizerMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZeroRead

theorem matrix_in_frame {k n Y A : Type} [CommRing k] [Fintype n] [DecidableEq n] [Fintype Y] [DecidableEq Y] [Fintype A]
    [DecidableEq A] (β : Matrix n Y k) (γ : Matrix Y n k) (h : γ * β = 1) (b : GL Y k) (σ : A ≃ Y) (e : A ≃ n)
    (X : Matrix A A k) (m : Matrix n n k)
    (hm : ((β * b.val).submatrix id fun i => σ (e.symm i)) * m =
      β * (b.val * X.submatrix σ.symm σ.symm * (b⁻¹).val) * γ * (β * b.val).submatrix id fun i => σ (e.symm i)) :
    m = X.submatrix e.symm e.symm := by
  let ρ : n ≃ Y := e.symm.trans σ
  have h1 : ((b⁻¹).val * γ) * (β * b.val) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc γ, h, Matrix.one_mul, Units.inv_mul]
  have h2 : β * (b.val * X.submatrix σ.symm σ.symm * (b⁻¹).val) * γ * (β * b.val) =
      β * b.val * X.submatrix σ.symm σ.symm := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc (b.val * _), ← Matrix.mul_assoc (b⁻¹).val, h1, Matrix.mul_one,
      Matrix.mul_assoc]
  have h3 : ∀ (P : Matrix n n k) (Q : Matrix n Y k), P * Q.submatrix id ρ = (P * Q).submatrix id ρ := fun _ _ => rfl
  have h4 : ∀ (P : Matrix Y n k) (Q : Matrix n Y k), P.submatrix ρ id * Q.submatrix id ρ = (P * Q).submatrix ρ ρ :=
    fun _ _ => rfl
  change (β * b.val).submatrix id ρ * m = _ * (β * b.val).submatrix id ρ at hm
  rw [h3, h2] at hm
  have h5 := congrArg (fun Z => ((b⁻¹).val * γ).submatrix ρ id * Z) hm
  try simp only at h5
  rw [← Matrix.mul_assoc, h4, h4, h1, ← Matrix.mul_assoc, h1, Matrix.submatrix_one_equiv, Matrix.one_mul, Matrix.one_mul] at h5
  rw [h5]
  ext i j
  simp [ρ]

theorem toEAf_onto (D : D7) : Function.Surjective (toEAf D) := by
  refine (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective.comp ?_
  exact Algebra.TensorProduct.map_surjective _ _ (fun α => ⟨pairA _ 0 α, rfl⟩) Function.surjective_id

theorem finE_val {D : D7} (V : HSp D) (g : GA D V) : (Lev.finE V g).val = (Formalism.L2.Theta.mt V g).map (toEAf D) := rfl

theorem upperLeftBlock_apply_of_eq {κ : Type} [CommRing κ] {r n : ℕ} (hr : r ≤ n) (hn : n ≤ r) (g : GL (Fin n) κ) (i j : Fin r) :
    (upperLeftBlock hr g).val i j = g.val (Fin.castLE hr i) (Fin.castLE hr j) := by
  have hg : g ∈ blockTri (κ := κ) (blk2 r) := fun i j h => by
    have hi : i.val < r := lt_of_lt_of_le i.2 hn
    have hj : j.val < r := lt_of_lt_of_le j.2 hn
    simp [blk2, hi, hj] at h
  rw [upper_block_val_submatrix hr hg]
  rfl


set_option maxHeartbeats 1000000 in
theorem red_of_isLoc : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP), d.Base → ∀ (hr : D.R.r ≤ (d.st 0).V.rank) (g : GA D (d.st 0).V) (x : G.S.P.J), (GlobalTheory.LocMod.ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) g (GlobalTheory.LevZeroGen.upZero G.S (Fin D.R.t) x.1) → finE (d.st 0).V ((d.t 0)⁻¹ * g * d.t 0) ∈ St (d.st 0).β → G.Red x (upperLeftBlock hr (redFn (d.st 0).β PP (finE (d.st 0).V ((d.t 0)⁻¹ * g * d.t 0)))) := by
  intro D u d τ PP G hB hr g x hg hS
  obtain ⟨π', h1, h2, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D G.k G.q PP G.idem
  obtain ⟨e, he, hM⟩ := G.frame 0 (G.s + 1) (Nat.zero_add _)
  obtain ⟨m, hm⟩ := hS
  choose f hf using toEAf_onto D
  have hπ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) (Formalism.L2.Theta.AE D)), (Z.map (toEAf D)).map π' = Z.map (GlobalTheory.LocMod.ofSplit G.q).π := fun Z => by
    ext i j; exact h1 _
  have hb : (((d.st 0).β.val.map f).map (toEAf D)) = (d.st 0).β.val := by ext i j; exact hf _
  have hM' := hM _ hb
  rw [← hπ, Matrix.map_mul (f := toEAf D), hb, ← finE_val] at hM'
  have hg2 := hg.2
  rw [← hπ, ← finE_val] at hg2
  have hmul : Lev.finE (d.st 0).V (d.t 0) * (d.st 0).β * intGL _ _ _ m =
      Lev.finE (d.st 0).V g * (Lev.finE (d.st 0).V (d.t 0) * (d.st 0).β) := by
    have : (d.st 0).β * intGL _ _ _ m * (d.st 0).β⁻¹ = _ := hm
    rw [map_mul, map_mul, map_inv] at this
    rw [mul_assoc, eq_mul_of_mul_inv_eq this]
    group
  have hmul' := congrArg (fun Z : GL (Fin (d.st 0).V.rank) (Lev.EAf D) => Z.val.map π') hmul
  simp only [Units.val_mul] at hmul'
  rw [Matrix.map_mul (L := _ * _), Matrix.map_mul (M := _ * _), hM', hg2] at hmul'
  have key := matrix_in_frame _ _ (G.FY 0 (G.s + 1) (Nat.zero_add _)).γβ _ _ e
    (x.1.val.submatrix (GlobalTheory.StepData.ixZero _ (Fin D.R.t)).symm (GlobalTheory.StepData.ixZero _ (Fin D.R.t)).symm) _ hmul'
  have hn : (d.st 0).V.rank ≤ D.R.r := by
    have := (hB.st 0 (by have := G.hs; omega)).rank
    rw [this]; simp [Formalism.BasicNotions.Ranks.rankY]
  intro a b a' b' ha hb' z hz
  rw [upperLeftBlock_apply_of_eq hr hn, ← hm, redFn_frGL] at hz
  have ea : e.symm (Fin.castLE hr a') = Sum.inl a := by
    rw [Equiv.symm_apply_eq]; apply Fin.ext; rw [he]; rcases a with a | a <;> exact ha
  have eb : e.symm (Fin.castLE hr b') = Sum.inl b := by
    rw [Equiv.symm_apply_eq]; apply Fin.ext; rw [he]; rcases b with b | b <;> exact hb'
  have k2 := congrFun (congrFun key (Fin.castLE hr a')) (Fin.castLE hr b')
  rw [Matrix.submatrix_apply, ea, eb] at k2
  have k3 : resS D.host.F PP (m.val (Fin.castLE hr a') (Fin.castLE hr b') - oToS D.host.F D.host.E z) = 0 := by
    rw [map_sub, resS_oToS, hz]; exact sub_self _
  have k4 := (h2.ker _).1 k3
  rw [map_sub] at k4
  have k5 : π' (oToS D.host.F D.host.E z).1 = (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) := by
    refine Eq.trans (congrArg π' ?_) (h1 (incA D (z : D.host.E)))
    rfl
  convert k4 using 3
  · exact k2.symm
  · exact k5.symm

end GlobalTheory.LevZeroRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelSliceFirstSummand
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SliceLeft

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac GlobalTheory.SliceLine

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def boxL (c : SB (Matrix n Unit k)) : SB (Matrix n n' k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) where
  toFun Ξ := box Ξ c
  map_add' Ξ Ξ' := Subtype.ext (funext fun x => by simp [box, splitCols, add_mul])
  map_smul' a Ξ := Subtype.ext (funext fun x => by simp [box, splitCols]; ring)

theorem heis_slice_left {S A L T : HSp D} (d : OrthDec S A L) (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ)
    (u u' : WO A T) (w : WO L T) :
    heisO ψ S T ((d.resS T).symm (u', 0)) f ((d.resS T).symm (u, w)) =
      heisO ψ A T u' (fun u => f ((d.resS T).symm (u, w))) u := by
  simp only [heisO]
  rw [d.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem isHalf_slice_left {S A L T : HSp D} (d : OrthDec S A L) {a : AE D} {y : WO A T} (hy : IsHalf a y) :
    IsHalf a ((d.resS T).symm (y, 0)) := by
  intro i j
  rw [resS_symm_apply, Matrix.zero_mul, add_zero, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, hy i l]

end GlobalTheory.SliceLeft

namespace GlobalTheory.SliceLeft

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac GlobalTheory.SliceLine

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {ρ : ℕ} {B : BesLev D ρ} {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)} {FL : Frame k B.L.rank Unit}

theorem up_fromCols_left (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) {S : HSp D}
    (FS : Frame k S.rank n) (x : Matrix n n' k) :
    p.up F₀ FS (fromCols x 0) = (B.o.resS S).symm (p.up FA FS x, 0) := by
  have k1 : x * FA.γ * B.o.qA.map (p.π.comp (incA D)) * F₀.β = fromCols x (0 : Matrix n Unit k) := by
    rw [beta_eq p h hL, Matrix.mul_fromCols]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (B.o.qA.map _) (B.o.iA.map _), ← Matrix.map_mul, B.o.qA_iA,
      ← Matrix.mul_assoc (B.o.qA.map _) (B.o.iB.map _), ← Matrix.map_mul, B.o.qA_iB]
    simp [FA.γβ]
  have k2 : fromCols x (0 : Matrix n Unit k) * F₀.γ = x * FA.γ * B.o.qA.map (p.π.comp (incA D)) := by
    rw [← k1, Matrix.mul_assoc (x * FA.γ * B.o.qA.map (p.π.comp (incA D))) F₀.β F₀.γ, F₀.βγ, Matrix.mul_one]
  rw [resS_symm_apply, Matrix.zero_mul, add_zero]
  unfold Place.up
  rw [pA, map_ι_mul, rat_map_π]
  congr 1
  rw [Matrix.mul_assoc FS.β (fromCols x 0) F₀.γ, k2]
  simp only [Matrix.mul_assoc]

theorem resS_up_fst (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) {S : HSp D}
    (FS : Frame k S.rank n) (t : Matrix n (n' ⊕ Unit) k) :
    (B.o.resS S (p.up F₀ FS t)).1 = p.up FA FS t.toCols₁ := by
  have k1 : t * F₀.γ * B.o.iA.map (p.π.comp (incA D)) * FA.β = t.toCols₁ := by
    calc t * F₀.γ * B.o.iA.map (p.π.comp (incA D)) * FA.β
        = ((t * F₀.γ) * fromCols (B.o.iA.map (p.π.comp (incA D)) * FA.β)
            (B.o.iB.map (p.π.comp (incA D)) * FL.β)).toCols₁ := by
          rw [Matrix.mul_fromCols, toCols₁_fromCols, Matrix.mul_assoc (t * F₀.γ)]
      _ = ((t * F₀.γ) * F₀.β).toCols₁ := by rw [← beta_eq p h hL]
      _ = t.toCols₁ := by rw [Matrix.mul_assoc, F₀.γβ, Matrix.mul_one]
  have k2 : t * F₀.γ * B.o.iA.map (p.π.comp (incA D)) = t.toCols₁ * FA.γ := by
    rw [← k1, Matrix.mul_assoc (t * F₀.γ * B.o.iA.map (p.π.comp (incA D))) FA.β FA.γ, FA.βγ, Matrix.mul_one]
  rw [resS_apply]
  dsimp only
  unfold Place.up
  rw [jA, map_ι_mul, rat_map_π]
  simp only [Matrix.mul_assoc] at k2 ⊢
  rw [k2]

end GlobalTheory.SliceLeft

namespace GlobalTheory.SliceLeft

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac GlobalTheory.SliceLine

theorem toCols_add_left {k n n' : Type} [Field k] (t : Matrix n (n' ⊕ Unit) k) (x : Matrix n n' k) :
    (t + fromCols x (0 : Matrix n Unit k)).toCols₁ = t.toCols₁ + x ∧
      (t + fromCols x (0 : Matrix n Unit k)).toCols₂ = t.toCols₂ :=
  ⟨by ext i j; simp, by ext i j; simp⟩

theorem slice_left : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∀ (c : SB (Matrix n Unit k)) (w₀ : WO B.L S), ∃ T', p.IsModel ψ FA FS T' ∧ ∀ (Ξ : SB (Matrix n n' k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → ∀ u, T' Ξ u = T₀ Ψ ((B.o.resS S).symm (u, w₀)) := by
  intro D k _ _ _ _ p ψ ρ B S s n n' _ _ _ _ FA F₀ FS h T₀ hT c w₀
  obtain ⟨FL, hFL, -⟩ := slice_line D k p ψ ρ B S s n n' FA F₀ FS h T₀ hT
  let T' : SB (Matrix n n' k) →ₗ[ℂ] (WO B.A S → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun u : WO B.A S => (B.o.resS S).symm (u, w₀))).comp (T₀.comp (boxL c))
  have hT' : ∀ Ξ u, T' Ξ u = T₀ (box Ξ c) ((B.o.resS S).symm (u, w₀)) := fun _ _ => rfl
  refine ⟨T', ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun Ξ Ψ hΨ u => ?_⟩
  · exact GlobalTheory.BoxSlice.isThetaFunO_slice_left B.o (hT.theta (box Φ c)) w₀
  · have e := hT.trans (fromCols x 0) (box Φ c) (box Φ' c) (fun t => by
      rw [box_apply, box_apply, hΦ, (toCols_add_left t x).1, (toCols_add_left t x).2])
    funext u
    rw [hT', e, up_fromCols_left p h hFL, heis_slice_left]
    rfl
  · have e := hT.modul ((B.o.resS S).symm (y, 0)) (isHalf_slice_left B.o hy) (box Φ c) (box Φ' c) (fun t => by
      simp only [box_apply, hΦ, B.o.symplO_resS, AddEquiv.apply_symm_apply, resS_up_fst p h hFL, symplO_zero_right',
        add_zero]
      ring)
    funext u
    rw [hT', e, heis_slice_left]
    rfl
  · have e : Ψ = box Ξ c := Subtype.ext (funext fun x => by rw [hΨ, box_apply]; rfl)
    rw [hT', e]

end GlobalTheory.SliceLeft
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumAtIdentityNonzeroConstant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.VacAllBase

theorem thetaSpace_std_line {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : ℕ) (hi : i + 1 ≤ B.R.m) : ∀ F ∈ Formalism.L2.Th1.H.Th (HV I.A.sc) (alV (I.rec7 l Z).host.d I.A.sc) (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1)))), ∃ c : ℂ, F = c • I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) := by
  intro F hF
  let Bk : Formalism.L2.Ker.Base (I.rec7 l Z) ⊤ I.J.δ := GlobalTheory.Mem.Col2.Th.VacIn.toRec (D := I.rec7 l Z) I.J.V
  have hS : Bk.StdOK := GlobalTheory.FourthRootStd.stdOK Bk (GlobalTheory.Glob.IntegralWittCoefficients.isCurveIdeal_top _)
    ((GlobalTheory.Mem.Col2.Th.isDiscriminantTwelfthRoot_host_iff (I.rec7 l Z) ⊤ I.J.δ).1 hI.amb_ok.delta)
  have hLa : LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) = Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) (Formalism.MainNotions.TaylorLogMetric.tor0 (I.rec7 l Z) ⊤ I.J.δ) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) := by
    rw [← Formalism.L2.KerInert.RepComb.lamK_eq, Formalism.L2.KerInert.RepComb.lamK, GlobalTheory.ThetaLineStd.aaOf_top]
    rfl
  have hH : (HV (ι := (I.rec7 l Z).what₂.Tau) (a := B.R.N i) (b := B.R.N (i + 1)) I.A.sc) = formV (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf (I.rec7 l Z) ⊤ I.J.δ)) (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) :=
    Formalism.L2.KerInert.RepComb.HV_eq_formV _
  rw [hLa, alV, hH] at hF
  have hF' : F ∈ Formalism.L2.Th1.H.Th (formV (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf (I.rec7 l Z) ⊤ I.J.δ)) (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1))) (Formalism.MainNotions.TaylorLogMetric.al (I.rec7 l Z) Bk.tor) (Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) Bk.tor (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1)))) := by
    refine Formalism.L2.Ker.Th_congr _ _ _ _ (fun x hx => ?_) hF
    obtain ⟨m, hm⟩ := Bk.qInt0 hS _ _ x hx
    exact (Formalism.L2.Ker.al_eq _ Bk.tor x m hm).symm
  obtain ⟨c, hc⟩ := Formalism.L2.PairingIndexBounds.Eq.J.thZeroSpans hS _ _ F hF'
  refine ⟨c, ?_⟩
  have hM : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) = Bk.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) := rfl
  obtain ⟨x, hx, hIx⟩ := GlobalTheory.NatAtStd.Iop_self (I.rec7 l Z) Bk.tor (Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) Bk.tor (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))))
  have hfix : (fun z => Formalism.MainNotions.TaylorLogMetric.al (I.rec7 l Z) Bk.tor x * Formalism.MainNotions.TaylorLogMetric.U (I.rec7 l Z) Bk.tor x (Bk.thZero (B.R.N i) (B.R.N (i + 1))) z) = Bk.thZero (B.R.N i) (B.R.N (i + 1)) :=
    funext fun z => (Bk.thZeroMem hS _ _).2 x hx z
  have hMz : Bk.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) = Bk.thZero (B.R.N i) (B.R.N (i + 1)) := by
    unfold Formalism.L2.Ker.Base.thMoved Formalism.L2.Ker.Base.thHalf
    rw [hIx, hIx, hfix, hfix]
  rw [hM, hMz]
  exact hc

theorem moveT_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac 1 1 := by
  intro B X I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om _ hom
  have hstd := (GlobalTheory.AdForm.StdStepsT.stdPair_steps_all I hI hP l Z ψ θ hψ hθ).1 i hi
  have key := _root_.GlobalTheory.MovedVac.vac_moved (I.rec7 l Z) ψ θ _ _ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi)
    I.A.δ I.A.sc hstd μ om hom vac hvac 1 (one_mem _) 1 (one_mem _)
  have S1 : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
      Moves V hn 1 N → N = Formalism.L2.Col.stdLat D.host.E n := _root_.GlobalTheory.AdForm.MovesOne.moves_one
  have S2 : ∀ (D : D7) (μ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D μ n → Even n → ∀ (V : HSp D) (x : (AE D)ˣ),
      IsDetRoot V 1 x → μ x = 1 := _root_.GlobalTheory.char_conj_fixed_eq_one
  have S3 := thetaSpace_std_line I hI l Z i hi
  by_cases hex : Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) 1 (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) ∧
      Moves _ (rankN (I.rec7 l Z) (i + 1) hi) 1 (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1)))
  · obtain ⟨-, hmem, hne⟩ := key _ _ hex.1 hex.2
    obtain ⟨c, hc⟩ := S3 _ hmem
    refine ⟨c, ?_, ?_⟩
    · rintro rfl
      apply hne
      exact hc.trans (zero_smul _ _)
    · intro N N' hN hN' x y hx hy
      obtain rfl := S1 _ _ _ _ N hN
      obtain rfl := S1 _ _ _ _ N' hN'
      have hx1 : μ x = 1 := S2 _ _ _ hom.resS hstd.rk.2.2.1 _ x hx
      have hy1 : μ y = 1 := S2 _ _ _ hom.resT hstd.rk.2.2.2 _ y hy
      rw [hx1, hy1]
      show xiN θ _ _ _ _ I.A.δ I.A.sc _ = _
      refine hc.trans ?_
      funext z
      simp only [Pi.smul_apply, smul_eq_mul, Circle.coe_one, inv_one, mul_one]
      rfl
  · refine ⟨1, one_ne_zero, ?_⟩
    intro N N' hN hN'
    exact absurd ⟨S1 _ _ _ _ N hN ▸ hN, S1 _ _ _ _ N' hN' ▸ hN'⟩ hex

end GlobalTheory.AdForm.VacAllBase
end
end

