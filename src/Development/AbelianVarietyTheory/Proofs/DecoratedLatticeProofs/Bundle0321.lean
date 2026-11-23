module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorIntertwinesTranslations
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatTrans

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem ι_sandwich (a c : AE D) (m : k) : p.ι (p.π a * m * p.π c) = a * p.ι m * c := by
  rw [GlobalTheory.LocChar.ι_mul, GlobalTheory.LocChar.ι_mul, p.ι_π, p.ι_π]
  have h := GlobalTheory.LocChar.e_mul_ι p m
  linear_combination (a * c * p.e + a * c) * h

theorem mul_map_ι_mul {a b l m : Type} [Fintype a] [Fintype b] (A : Matrix m a (AE D)) (M : Matrix a b k)
    (C : Matrix b l (AE D)) : A * M.map p.ι * C = (A.map p.π * M * C.map p.π).map p.ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul, map_sum, ι_sandwich]

theorem map_incA_map {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) : (M.map (incA D)).map p.π = M.map p.pr := by
  ext; rfl

theorem ι_mem_idAt : ∃ v, ∀ y : k, p.ι y ∈ GlobalTheory.FinPl.idAt D (· = v) := by
  obtain ⟨-, he, v, ε, hε, hsum⟩ := p.split
  refine ⟨v, fun y => GlobalTheory.FinPl.Model.mem_idAt_iff.2 ?_⟩
  have hε' := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 hε
  subst hε'
  rw [← hsum]
  have h1 := GlobalTheory.LocChar.e_mul_ι p y
  have h2 : cA D p.e * p.e = 0 := by rw [mul_comm]; exact he
  linear_combination (1 - cA D p.e) * h1 + p.ι y * h2

theorem sb_translate {X : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X] {Φ : X → ℂ}
    (hΦ : Φ ∈ SB X) (t : X) : (fun z => Φ (z + t)) ∈ SB X :=
  ⟨hΦ.1.comp_continuous (continuous_add_const t), hΦ.2.comp_homeomorph (Homeomorph.addRight t)⟩

section Local
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def bigPt (c ρ : ℕ) (x : Matrix n (n' ⊕ Unit) k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  fromBlocks x.toCols₁ (Matrix.of fun r i => if i.val = ρ then x r (Sum.inr ()) else 0) 0 0

theorem flCol_translate [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) (c ρ : ℕ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x t : Matrix n (n' ⊕ Unit) k) :
    GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) (fun z => Φ (z + bigPt c ρ x)) t = GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ (t + x) := by
  unfold GlobalTheory.LocFlat.flCol GlobalTheory.RootEx.opE
  congr 1
  funext e
  have h1 : affPt (ρ + 1) t.toCols₁ e + GlobalTheory.LocFlat.colAt n' c (ρ + 1) (fun r => t r (Sum.inr ())) + bigPt c ρ x =
      affPt (ρ + 1) (t + x).toCols₁ e + GlobalTheory.LocFlat.colAt n' c (ρ + 1) (fun r => (t + x) r (Sum.inr ())) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [affPt, basePt, GlobalTheory.LocFlat.colAt, bigPt, add_right_comm]
    · by_cases h : j.val = ρ <;> simp [affPt, basePt, GlobalTheory.LocFlat.colAt, bigPt, h, add_assoc]
    · simp [affPt, basePt, GlobalTheory.LocFlat.colAt, bigPt]
    · simp [affPt, basePt, GlobalTheory.LocFlat.colAt, bigPt]
  have h2 : ch (affPt (ρ + 1) t.toCols₁ e) = ch (affPt (ρ + 1) (t + x).toCols₁ e) := by
    simp [ch, affPt, basePt]
  simp only [h1, h2]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq n] [DecidableEq n'] in
theorem mul_bigPt_mul {a b : Type} {c ρ : ℕ} (j₀ : Fin (c + 1)) (hj : j₀.val = ρ) (β : Matrix a (n ⊕ Fin c) k) (β₀ : Matrix a n k)
    (γ : Matrix (n' ⊕ Fin (c + 1)) b k) (γ₀ : Matrix (n' ⊕ Unit) b k) (hβ : ∀ r i, β r (Sum.inl i) = β₀ r i)
    (hγ : ∀ i s, γ (Sum.inl i) s = γ₀ (Sum.inl i) s) (hγ' : ∀ s, γ (Sum.inr j₀) s = γ₀ (Sum.inr ()) s)
    (x : Matrix n (n' ⊕ Unit) k) : β * bigPt c ρ x * γ = β₀ * x * γ₀ := by
  ext r s
  have hj' : ∀ j : Fin (c + 1), j.val = ρ ↔ j = j₀ := fun j => by rw [← hj, Fin.val_inj]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, bigPt, hβ, hγ, hj', hγ', Finset.sum_ite_irrel]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem rows_of_inverse {N N₀ c : ℕ} (j₀ : Fin (c + 1)) (F : Frame k N (n' ⊕ Fin (c + 1))) (F₀ : Frame k N₀ (n' ⊕ Unit))
    (q : Matrix (Fin N₀) (Fin N) k) (h1 : ∀ r i, (q * F.β) r (Sum.inl i) = F₀.β r (Sum.inl i))
    (h2 : ∀ r, (q * F.β) r (Sum.inr j₀) = F₀.β r (Sum.inr ())) (h3 : ∀ r j, j ≠ j₀ → (q * F.β) r (Sum.inr j) = 0) :
    (∀ i s, F.γ (Sum.inl i) s = (F₀.γ * q) (Sum.inl i) s) ∧ ∀ s, F.γ (Sum.inr j₀) s = (F₀.γ * q) (Sum.inr ()) s := by
  let σ : n' ⊕ Unit → n' ⊕ Fin (c + 1) := Sum.map id fun _ => j₀
  have hq : F₀.β * F.γ.submatrix σ id = q := by
    conv_rhs => rw [← Matrix.mul_one q, ← F.βγ, ← Matrix.mul_assoc]
    ext r s
    rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_sum_type,
      Finset.sum_eq_single j₀ (fun j _ hj => by rw [h3 r j hj, zero_mul]) (by simp), h2]
    simp [h1, σ]
  have hγ : F₀.γ * q = F.γ.submatrix σ id := by rw [← hq, ← Matrix.mul_assoc, F₀.γβ, Matrix.one_mul]
  rw [hγ]
  exact ⟨fun _ _ => rfl, fun _ => rfl⟩

end Local

theorem proj_laws {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    d.p0.map p.π * d.i₀.map p.pr = 1 ∧ d.p0.map p.π * d.e.map p.pr = 0 ∧ d.p0.map p.π * d.e'.map p.pr = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_incA_map, ← Matrix.map_mul]
    exact (congrArg (·.map p.π) d.p0_j0).trans (Matrix.map_one _ (map_zero _) (map_one _))
  · rw [← map_incA_map, ← Matrix.map_mul]
    exact (congrArg (·.map p.π) d.p0_jX).trans (Matrix.map_zero _ (map_zero _))
  · rw [← map_incA_map, ← Matrix.map_mul]
    exact (congrArg (·.map p.π) d.p0_jY).trans (Matrix.map_zero _ (map_zero _))

def prHom : D.host.E →+* k := p.π.comp (incA D)

theorem pr_eq : p.pr = prHom p := rfl

theorem up_bigPt {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) (s hh : k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] {c : ℕ} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c))
    (hC : p.IsCoreFrame B s FA F₀) (hB : p.IsBesFrame B s FA FV) (hJ : p.IsJacFrame J s hh G₀ FW)
    (x : Matrix n (n' ⊕ Unit) k) :
    p.up FV FW (bigPt c ρ x) = B.d.ext0 J.W (J.d.inc0 B.V₀ (p.up F₀ G₀ x)) := by
  obtain ⟨hc, hinl, hlt, heq, hgt⟩ := hB
  obtain ⟨q1, q2, q3⟩ := proj_laws p B.d
  let j₀ : Fin (c + 1) := ⟨ρ, by omega⟩
  have col : ∀ (r : Fin B.V₀.rank) (j : n' ⊕ Fin (c + 1)) (a : k) (y : Fin B.V.rank → k), (∀ r', FV.β r' j = a * y r') →
      (B.d.p0.map p.π * FV.β) r j = a * (B.d.p0.map p.π *ᵥ y) r := fun r j a y h => by
    simp only [Matrix.mul_apply, h, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
  obtain ⟨g1, g2⟩ := rows_of_inverse j₀ FV F₀ (B.d.p0.map p.π)
    (fun r i => by
      rw [hC.1, ← Matrix.one_mul (B.o.iA.map p.pr * FA.β), ← q1, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun r' _ => ?_
      rw [hinl, pr_eq, Matrix.map_mul, Matrix.mul_assoc])
    (fun r => by
      rw [col r _ s (B.d.i₀.map p.pr *ᵥ fun i => p.pr (vecB B.o B.ζ i)) fun r' => by
        rw [heq j₀ rfl, pr_eq, RingHom.map_mulVec]; rfl, Matrix.mulVec_mulVec, q1, Matrix.one_mulVec, hC.2])
    (fun r j hj => by
      have hj' : j.val ≠ ρ := fun h => hj (Fin.ext h)
      rcases lt_or_gt_of_ne hj' with h | h
      · rw [col r _ _ _ (hlt ⟨j.val, h⟩ j rfl)]
        exact mul_eq_zero_of_right _ (congrFun (congrFun q2 r) ⟨j.val, h⟩)
      · have := j.2
        rw [col r _ _ _ (hgt ⟨2 * ρ - j.val, by omega⟩ j (by simp only; omega))]
        exact mul_eq_zero_of_right _ (congrFun (congrFun q3 r) ⟨2 * ρ - j.val, by omega⟩))
  rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Place.up, Place.up,
    mul_bigPt_mul j₀ rfl FW.β _ FV.γ _ hJ.2.1 g1 g2, ← map_incA_map]
  refine Eq.trans ?_ (mul_map_ι_mul p J.d.j0 _ B.d.p0).symm
  simp only [Matrix.mul_assoc]
  rfl

theorem factor_trans : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ)), (∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ) → ∀ (x : Matrix n (n' ⊕ Unit) k) (Ψ Ψ' : SB (Matrix n (n' ⊕ Unit) k)), (∀ t, Ψ'.1 t = Ψ.1 (t + x)) → L₀ Ψ' = heisO ψ B.V₀ J.W₀ (p.up F₀ G₀ x) (L₀ Ψ) := by
  intro D _ hFLs _ k _ _ _ _ _ _ p ν hν ψ ψk hpc ρ B J st s _ n n' _ _ _ _ c FA F₀ FV G₀ FW hC hB hJ Tm hTm L₀ hL₀ x Ψ Ψ' hΨ
  have hψc : Continuous ψk := ((_root_.GlobalTheory.LocChar.weil_char_split D k p ψ st.weil.std).2.1 ψk hpc).1
  have hc : c = 2 * ρ := hJ.1
  obtain ⟨Φ, hΦ, hΦΨ⟩ := ((_root_.GlobalTheory.LocFlat.flat_SB_onto k ψk ν hψc hν n n' c (ρ + 1) (by omega)).1 (by omega)).2 Ψ.1 Ψ.2
  have h1 : flatBF st (Tm ⟨Φ, hΦ⟩) = L₀ Ψ := hL₀ _ _ hΦΨ.symm
  have h2 : flatBF st (Tm ⟨_, sb_translate hΦ (bigPt c ρ x)⟩) = L₀ Ψ' := hL₀ _ _ (by
    funext t
    rw [hΨ, ← hΦΨ]
    exact (flCol_translate ψk ν c ρ Φ x t).symm)
  have h3 := hTm.trans (bigPt c ρ x) ⟨Φ, hΦ⟩ ⟨_, sb_translate hΦ (bigPt c ρ x)⟩ fun _ => rfl
  obtain ⟨v, hv⟩ := ι_mem_idAt p
  rw [← h2, h3, up_bigPt p B J s _ FA F₀ FV G₀ FW hC hB hJ, ← h1]
  exact ((hFLs ψ (· = v)).1 ρ B J st).Heisenberg₂.core _ (hTm.theta _) _ fun i j => hv _

end GlobalTheory.FlatTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelRestrictedToLineSlice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SliceLine

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem ι_mul (x : k) (b : AE D) : p.ι x * b = p.ι (x * p.π b) := by
  have h : p.ι (x * p.π b) = p.e * (p.ι x * b) := by
    calc p.ι (x * p.π b) = p.ι (p.π (p.ι x) * p.π b) := by rw [p.π_ι]
      _ = p.ι (p.π (p.ι x * b)) := by rw [p.π.map_mul]
      _ = p.e * (p.ι x * b) := p.ι_π _
  rw [h, ← mul_assoc, GlobalTheory.LocMod.Witness.e_ι]

theorem map_ι_mul {a b c : Type} [Fintype b] (M : Matrix a b k) (N : Matrix b c (AE D)) :
    M.map p.ι * N = (M * N.map p.π).map p.ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem frame_card {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) : Fintype.card Y = N := by
  have e : (Y → k) ≃ₗ[k] (Fin N → k) := LinearEquiv.ofLinearMap (Matrix.toLin' F.β) (Matrix.toLin' F.γ)
    (by rw [← Matrix.toLin'_mul, F.βγ, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, F.γβ, Matrix.toLin'_one])
  simpa using e.finrank_eq

def splitCols (n n' : Type) : Matrix n (n' ⊕ Unit) k ≃ₜ Matrix n n' k × Matrix n Unit k where
  toFun x := (x.toCols₁, x.toCols₂)
  invFun q := fromCols q.1 q.2
  left_inv x := fromCols_toCols x
  right_inv q := by simp
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_matrix fun i j => continuous_id.matrix_elem i (Sum.inl j)
    · exact continuous_matrix fun i j => continuous_id.matrix_elem i (Sum.inr j)
  continuous_invFun := by
    refine continuous_matrix fun i j => ?_
    cases j with
    | inl a => exact continuous_fst.matrix_elem i a
    | inr u => exact continuous_snd.matrix_elem i u

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def box (Ξ : SB (Matrix n n' k)) : SB (Matrix n Unit k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) where
  toFun c := comapH (splitCols n n') (prodSB Ξ c)
  map_add' c c' := Subtype.ext (funext fun x => by simp [splitCols, mul_add])
  map_smul' a c := Subtype.ext (funext fun x => by simp [splitCols]; ring)

theorem box_apply (Ξ : SB (Matrix n n' k)) (c : SB (Matrix n Unit k)) (x : Matrix n (n' ⊕ Unit) k) :
    (box Ξ c).1 x = Ξ.1 x.toCols₁ * c.1 x.toCols₂ := rfl

end GlobalTheory.SliceLine

namespace GlobalTheory.SliceLine

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem heis_slice {S A L T : HSp D} (d : OrthDec S A L) (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ)
    (u : WO A T) (w v : WO L T) :
    heisO ψ S T ((d.resS T).symm (0, v)) f ((d.resS T).symm (u, w)) =
      heisO ψ L T v (fun w => f ((d.resS T).symm (u, w))) w := by
  simp only [heisO]
  rw [d.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, zero_add,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

theorem isHalf_slice {S A L T : HSp D} (d : OrthDec S A L) {a : AE D} {y : WO L T} (hy : IsHalf a y) :
    IsHalf a ((d.resS T).symm (0, y)) := by
  intro i j
  rw [resS_symm_apply, Matrix.zero_mul, zero_add, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, hy i l]

variable {ρ : ℕ} {B : BesLev D ρ} {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)} {FL : Frame k B.L.rank Unit}

theorem beta_eq (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) :
    F₀.β = fromCols (B.o.iA.map (p.π.comp (incA D)) * FA.β) (B.o.iB.map (p.π.comp (incA D)) * FL.β) := by
  ext r (a | u)
  · exact h.1 r a
  · cases u
    rw [h.2 r, fromCols_apply_inr, Matrix.mul_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [vecB, Matrix.mulVec, dotProduct, Place.pr, map_sum, map_mul, Matrix.map_apply, hL, RingHom.comp_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

end GlobalTheory.SliceLine

namespace GlobalTheory.SliceLine

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {ρ : ℕ} {B : BesLev D ρ} {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)} {FL : Frame k B.L.rank Unit}

theorem rat_map_π {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) : (rat M).map p.π = M.map (p.π.comp (incA D)) := rfl

theorem up_fromCols (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) {S : HSp D}
    (FS : Frame k S.rank n) (x : Matrix n Unit k) :
    p.up F₀ FS (fromCols 0 x) = (B.o.resS S).symm (0, p.up FL FS x) := by
  have k1 : x * FL.γ * B.o.qB.map (p.π.comp (incA D)) * F₀.β = fromCols (0 : Matrix n n' k) x := by
    rw [beta_eq p h hL, Matrix.mul_fromCols]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (B.o.qB.map _) (B.o.iA.map _), ← Matrix.map_mul, B.o.qB_iA,
      ← Matrix.mul_assoc (B.o.qB.map _) (B.o.iB.map _), ← Matrix.map_mul, B.o.qB_iB]
    simp [FL.γβ]
  have k2 : fromCols (0 : Matrix n n' k) x * F₀.γ = x * FL.γ * B.o.qB.map (p.π.comp (incA D)) := by
    rw [← k1, Matrix.mul_assoc (x * FL.γ * B.o.qB.map (p.π.comp (incA D))) F₀.β F₀.γ, F₀.βγ, Matrix.mul_one]
  rw [resS_symm_apply, Matrix.zero_mul, zero_add]
  unfold Place.up
  rw [pB, map_ι_mul, rat_map_π]
  congr 1
  rw [Matrix.mul_assoc FS.β (fromCols 0 x) F₀.γ, k2]
  simp only [Matrix.mul_assoc]

theorem resS_up_snd (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) {S : HSp D}
    (FS : Frame k S.rank n) (t : Matrix n (n' ⊕ Unit) k) :
    (B.o.resS S (p.up F₀ FS t)).2 = p.up FL FS t.toCols₂ := by
  have k1 : t * F₀.γ * B.o.iB.map (p.π.comp (incA D)) * FL.β = t.toCols₂ := by
    calc t * F₀.γ * B.o.iB.map (p.π.comp (incA D)) * FL.β
        = ((t * F₀.γ) * fromCols (B.o.iA.map (p.π.comp (incA D)) * FA.β)
            (B.o.iB.map (p.π.comp (incA D)) * FL.β)).toCols₂ := by
          rw [Matrix.mul_fromCols, toCols₂_fromCols, Matrix.mul_assoc (t * F₀.γ)]
      _ = ((t * F₀.γ) * F₀.β).toCols₂ := by rw [← beta_eq p h hL]
      _ = t.toCols₂ := by rw [Matrix.mul_assoc, F₀.γβ, Matrix.mul_one]
  have k2 : t * F₀.γ * B.o.iB.map (p.π.comp (incA D)) = t.toCols₂ * FL.γ := by
    rw [← k1, Matrix.mul_assoc (t * F₀.γ * B.o.iB.map (p.π.comp (incA D))) FL.β FL.γ, FL.βγ, Matrix.mul_one]
  rw [resS_apply]
  dsimp only
  unfold Place.up
  rw [jB, map_ι_mul, rat_map_π]
  simp only [Matrix.mul_assoc] at k2 ⊢
  rw [k2]

end GlobalTheory.SliceLine

namespace GlobalTheory.SliceLine

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac

theorem toCols_add {k n n' : Type} [Field k] (t : Matrix n (n' ⊕ Unit) k) (x : Matrix n Unit k) :
    (t + fromCols (0 : Matrix n n' k) x).toCols₁ = t.toCols₁ ∧ (t + fromCols (0 : Matrix n n' k) x).toCols₂ = t.toCols₂ + x :=
  ⟨by ext i j; simp, by ext i j; simp⟩

theorem slice_line : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∃ FL : Frame k B.L.rank Unit, (∀ r, FL.β r () = s * p.pr (B.ζ r)) ∧ ∀ (Ξ : SB (Matrix n n' k)) (u₀ : WO B.A S), ∃ T', p.IsModel ψ FL FS T' ∧ ∀ (c : SB (Matrix n Unit k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → ∀ w, T' c w = T₀ Ψ ((B.o.resS S).symm (u₀, w)) := by
  intro D k _ _ _ _ p ψ ρ B S s n n' _ _ _ _ FA F₀ FS h T₀ hT
  have hA := frame_card FA
  have h0 := frame_card F₀
  have hr := B.o.rank_add
  rw [Fintype.card_sum, Fintype.card_unit] at h0
  have hL1 : B.L.rank = 1 := by omega
  have hsub : ∀ r r' : Fin B.L.rank, r = r' := fun r r' => Fin.ext (by have := r.isLt; have := r'.isLt; omega)
  have hv : ∀ r, s * p.pr (B.ζ r) ≠ 0 := by
    intro r₀ h₀
    have hz : ∀ r, s * p.pr (B.ζ r) = 0 := fun r => by rw [hsub r r₀]; exact h₀
    have hcol : ∀ r, F₀.β r (Sum.inr ()) = 0 := by
      intro r
      rw [h.2 r]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [vecB, Matrix.mulVec, dotProduct, Place.pr, map_sum, map_mul, Finset.mul_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := hz j
      simp only [Place.pr] at this
      rw [mul_left_comm, this, mul_zero]
    have := congrFun (congrFun F₀.γβ (Sum.inr ())) (Sum.inr ())
    simp [Matrix.mul_apply, hcol] at this
  obtain ⟨FL, hFL⟩ : ∃ FL : Frame k B.L.rank Unit, ∀ r, FL.β r () = s * p.pr (B.ζ r) := by
    refine ⟨⟨Matrix.of fun r _ => s * p.pr (B.ζ r), Matrix.of fun _ r => (s * p.pr (B.ζ r))⁻¹, ?_, ?_⟩, fun r => rfl⟩
    · ext r r'
      obtain rfl := hsub r r'
      simp [Matrix.mul_apply]
      rw [← _root_.mul_inv_rev]
      exact mul_inv_cancel₀ (hv r)
    · ext u u'
      simp [Matrix.mul_apply]
      rw [Finset.sum_congr rfl (g := fun _ => (1 : k)) fun j _ => by rw [← _root_.mul_inv_rev]; exact inv_mul_cancel₀ (hv j)]
      simp [hL1]
  refine ⟨FL, hFL, fun Ξ u₀ => ?_⟩
  let T' : SB (Matrix n Unit k) →ₗ[ℂ] (WO B.L S → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun w : WO B.L S => (B.o.resS S).symm (u₀, w))).comp (T₀.comp (box Ξ))
  have hT' : ∀ c w, T' c w = T₀ (box Ξ c) ((B.o.resS S).symm (u₀, w)) := fun _ _ => rfl
  refine ⟨T', ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun c Ψ hΨ w => ?_⟩
  · let f := T₀ (box Ξ Φ)
    have hf : IsThetaFunO ψ B.V₀ S f := hT.theta (box Ξ Φ)
    let e := (B.o.resS S).symm
    let incl : WO B.L S →+ WO B.V₀ S := sandwich (1 : Mx D S.rank S.rank) B.o.pB
    have he (v : WO B.L S) : incl v = e (0, v) := by
      rw [sandwich_apply, Matrix.one_mul, resS_symm_apply, Matrix.zero_mul, zero_add]
    have hadd (w v : WO B.L S) : e (u₀, w + v) = e (u₀, w) + incl v := by
      rw [he, ← map_add e, Prod.mk_add_mk, add_zero]
    have hslice : IsThetaFunO ψ B.L S (fun w => f (e (u₀, w))) := by
      refine ⟨?_, ?_, hf.cont.comp ((B.o.continuous_resS_symm S).comp
        (continuous_const.prodMk continuous_id)), ?_⟩
      · intro γ w
        have hrat : e (0, ratW S B.L γ) = ratW S B.V₀ (γ * B.o.qB) := by
          rw [resS_symm_apply, Matrix.zero_mul, zero_add, ratW_eq, ratW_eq, rat_mul]; rfl
        rw [add_comm (ratW S B.L γ) w, hadd, he, add_comm (e (u₀, w)), hrat, hf.quasi,
          ← hrat, B.o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
          GlobalTheory.MixModel.symplOH_zero_left, zero_add]
      · obtain ⟨U, hU, hlevel⟩ := hf.level
        refine ⟨U.comap incl, hU.preimage (continuous_sandwich _ _), fun v hv hzero => ?_⟩
        funext w
        have h := congrFun (hlevel (incl v) hv (map_sandwich _ _ _ hzero)) (e (u₀, w))
        rw [he, heis_slice] at h
        exact h
      · intro m L hL hzero w
        simp only [hadd]
        exact hf.smooth m (incl.comp L) ((continuous_sandwich _ _).comp hL)
          (fun t => map_sandwich _ _ _ (hzero t)) _
    exact hslice
  · have e := hT.trans (fromCols 0 x) (box Ξ Φ) (box Ξ Φ') (fun t => by
      rw [box_apply, box_apply, hΦ, (toCols_add t x).1, (toCols_add t x).2])
    funext w
    rw [hT', e, up_fromCols p h hFL, heis_slice]
    rfl
  · have e := hT.modul ((B.o.resS S).symm (0, y)) (isHalf_slice B.o hy) (box Ξ Φ) (box Ξ Φ') (fun t => by
      simp only [box_apply, hΦ, B.o.symplO_resS, AddEquiv.apply_symm_apply, resS_up_snd p h hFL, symplO_zero_right',
        zero_add]
      ring)
    funext w
    rw [hT', e, heis_slice]
    rfl
  · have e : Ψ = box Ξ c := Subtype.ext (funext fun x => by rw [hΨ, box_apply]; rfl)
    rw [hT', e]

end GlobalTheory.SliceLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateThetaFunLeSchwartzMajorantLevel
section
namespace I195MixedCoordinates_817fca156a590a31b0ba19c7

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_817fca156a590a31b0ba19c7

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.Unf

theorem le_mul_ofReal_inv_of_mul_le {a b : ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) (N : ℕ)
    (h : a * ENNReal.ofReal ((1 + r) ^ N) ≤ b) : a ≤ b * ENNReal.ofReal (((1 + r) ^ N)⁻¹) := by
  have hpos : 0 < (1 + r) ^ N := by positivity
  rw [ENNReal.ofReal_inv_of_pos hpos, ← div_eq_mul_inv]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hpos)) (Or.inl ENNReal.ofReal_ne_top)]
  exact h

theorem mixS_le_maj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (U : AddSubgroup (WO S T)),
    IsOpen (U : Set (WO S T)) → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ N : ℕ, ∃ C : ℝ≥0,
    ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ x w,
      ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ ≤ C * supSob ψ θ N f * ENNReal.ofReal (maj θ K N x) := by
  intro D ψ hψ θ hθ S S₀ T ρ d v U hU
  obtain ⟨K, hK, hsupp⟩ := _root_.GlobalTheory.Unf.mixS_support_inBox D ψ hψ S S₀ T ρ d v U hU
  refine ⟨K, hK, fun N => ?_⟩
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.Unf.mixS_decay D ψ hψ θ hθ S S₀ T ρ d v N
  refine ⟨C, fun f hf x w => ?_⟩
  by_cases h0 : (_root_.I195MixedCoordinates_817fca156a590a31b0ba19c7.source d) T ψ v.μ v.𝓕 f x w = 0
  · change ‖(_root_.I195MixedCoordinates_817fca156a590a31b0ba19c7.source d) T ψ v.μ v.𝓕 f x w‖ₑ ≤ _
    rw [h0]; simp
  · have hbox := hsupp f hf x w h0
    have hmaj : maj θ K N x = ((1 + realSize θ x) ^ N)⁻¹ := by
      unfold maj; rw [if_pos hbox]
    rw [hmaj]
    exact le_mul_ofReal_inv_of_mul_le (realSize_nonneg θ x) N (hC f hf.1 x w)

end GlobalTheory.Unf
end

