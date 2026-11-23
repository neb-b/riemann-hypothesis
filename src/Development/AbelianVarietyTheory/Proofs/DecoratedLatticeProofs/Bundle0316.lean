module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapSupportFirstHalfAtLevelPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData GlobalTheory.SymChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.SuppFirst

theorem e_mul_ι {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x : k) : p.e * p.ι x = p.ι x := by
  rw [← p.ι_π, p.π_ι]

theorem ι_mul' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  have h := p.ι_π (p.ι x * p.ι y)
  rw [map_mul, p.π_ι, p.π_ι, ← mul_assoc, e_mul_ι] at h
  exact h

theorem ι_one' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : p.ι 1 = p.e := by
  have h := p.ι_π 1
  rwa [map_one, mul_one] at h

theorem shift_mul {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x y : k) :
    (p.ι x + (1 - p.e)) * (p.ι y + (1 - p.e)) = p.ι (x * y) + (1 - p.e) := by
  have he : p.e * p.e = p.e := p.split.1
  have h1 : p.ι x * (1 - p.e) = 0 := by
    rw [mul_sub, mul_one, mul_comm, e_mul_ι, sub_self]
  have h2 : (1 - p.e) * p.ι y = 0 := by
    rw [sub_mul, one_mul, e_mul_ι, sub_self]
  have h3 : (1 - p.e) * (1 - p.e) = 1 - p.e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  rw [ι_mul', add_mul, mul_add, mul_add, h1, h2, h3, add_zero, zero_add]

def shiftU {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : kˣ →* (AE D)ˣ where
  toFun x := ⟨p.ι x + (1 - p.e), p.ι (x⁻¹ : kˣ) + (1 - p.e), by
      rw [shift_mul, Units.mul_inv, ι_one']; ring, by
      rw [shift_mul, Units.inv_mul, ι_one']; ring⟩
  map_one' := by ext; simp [ι_one']
  map_mul' x y := by ext; simp [shift_mul]

theorem exists_comp {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (χ : (AE D)ˣ →* Circle) : ∃ μ : kˣ →* ℂˣ, p.IsComp χ μ := by
  refine ⟨Circle.toUnits.comp (χ.comp (shiftU p)), fun x a ha => ?_⟩
  have : shiftU p x = a := Units.ext ha.symm
  simp [this]

theorem card_frame {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (Fr : Frame k N Y) :
    Fintype.card Y = N := by
  apply le_antisymm
  · have h := Matrix.rank_mul_le_left Fr.γ Fr.β
    rw [Fr.γβ, Matrix.rank_one] at h
    have h' := Matrix.rank_le_card_width Fr.γ
    rw [Fintype.card_fin] at h'
    exact h.trans h'
  · have h := Matrix.rank_mul_le_left Fr.β Fr.γ
    rw [Fr.βγ, Matrix.rank_one, Fintype.card_fin] at h
    exact h.trans (Matrix.rank_le_card_width Fr.β)

def prH {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : D.host.E →+* k := p.π.comp (incA D)

theorem prH_apply {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (a : D.host.E) : prH p a = p.pr a := rfl

theorem exists_coreFrame {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} {n₀ n₁ n₂ : Type}
    [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] {c : ℕ}
    (F : Dbl p B J B' n₀ n₁ n₂ c) : ∃ C : Frame k B.V₀.rank (n₀ ⊕ Unit), p.IsCoreFrame B F.s F.F₀ C := by
  obtain ⟨hc, hA, -, hz, -⟩ := F.bes
  let M : Matrix (Fin B.V₀.rank) (n₀ ⊕ Unit) k :=
    fromCols (B.o.iA.map p.pr * F.F₀.β) (Matrix.of fun r (_ : Unit) => F.s * p.pr (vecB B.o B.ζ r))
  let f : n₀ ⊕ Unit → n₀ ⊕ Fin (c + 1 + 1 + 1) := Sum.elim Sum.inl fun _ => Sum.inr ⟨σ + 1, by omega⟩
  have hf : Function.Injective f := by
    rintro (a | _) (b | _) h <;> simp_all [f]
  have key : B.d.i₀.map p.pr * M = F.G₀.β.submatrix id f := by
    ext r (a | _)
    · simp only [M, f, Matrix.mul_fromCols, fromCols_apply_inl, submatrix_apply, id, Sum.elim_inl]
      rw [hA r a, ← Matrix.mul_assoc]
      have hm : B.d.i₀.map p.pr * B.o.iA.map p.pr = (B.d.i₀ * B.o.iA).map p.pr :=
        (Matrix.map_mul (f := prH p)).symm
      rw [hm]
    · simp only [M, f, Matrix.mul_fromCols, fromCols_apply_inr, submatrix_apply, id, Sum.elim_inr]
      rw [hz ⟨σ + 1, by omega⟩ rfl r]
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, mulVec, dotProduct]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← prH_apply, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_mul, prH_apply, prH_apply]
      ring
  let L : Matrix (n₀ ⊕ Unit) (Fin B.V₀.rank) k := F.G₀.γ.submatrix f id * B.d.i₀.map p.pr
  have hLM : L * M = 1 := by
    simp only [L, Matrix.mul_assoc, key]
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, F.G₀.γβ]
    exact Matrix.submatrix_one _ hf
  have hcard : Fintype.card (n₀ ⊕ Unit) = B.V₀.rank := by
    have h1 := card_frame F.G₀
    have h2 := B.d.rank_add
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at h1 ⊢
    omega
  have hML : M * L = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (n₀ ⊕ Unit) (Fin B.V₀.rank) k (A := L) (B := M) (by simpa using hcard)).mp hLM
  refine ⟨⟨M, L, hML, hLM⟩, fun r a => ?_, fun r => ?_⟩
  · simp [M]
  · simp [M]

theorem isLoc_one {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (Fr : Frame k V.rank Y) : p.IsLoc Fr 1 1 := by
  obtain ⟨hloc, -, -⟩ := _root_.GlobalTheory.LocGrp.local_groups D k p
  obtain ⟨g₀, hg₀, hu⟩ := (hloc V Y Fr).1 1
  have h2 := (hloc V Y Fr).2.2 _ _ _ _ hg₀ hg₀
  rw [mul_one] at h2
  have e : g₀ * g₀ = g₀ := hu _ h2
  have : g₀ = 1 := by
    have := congrArg (g₀⁻¹ * ·) e
    simpa [← mul_assoc] using this
  exact this ▸ hg₀

theorem gsupp1 : ∀ (D : D7), OmLoc D → FlatBF D → GlobalTheory.LocFlat.SymCollapse → GSupp1 D := by
  intro D hOm hFl hSym k _ _ _ _ p s κ S t _ _ ψ hψ j c H σ B J B' F s₁ hμ T₁ hT₁ Φ₁ hΦ₁ h hh hne
  obtain ⟨hloc, hjac, -⟩ := _root_.GlobalTheory.LocGrp.local_groups D k p
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := exists_isUnitVol k
  haveI := hν.1
  obtain ⟨hk, hhk⟩ := (hloc J.W _ F.G₁).2.1 h hh
  have hc : c = 2 * σ := by have := F.bes.1; omega

  obtain ⟨μT, hT⟩ := exists_comp p s₁.χW
  have hS : p.IsComp s₁.χV (S.μ (j + 1))⁻¹ := by
    intro x a ha
    have := hμ x a ha
    simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Circle.coe_inv] at this ⊢
    rw [this, inv_inv]

  let Φ' : SB (Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1 + 1)) k) :=
    ⟨om (S.μ (j + 1)) 1 hk Φ₁.1, om_mem_SB (μ := S.μ (j + 1)) (1 : GL _ k) hk Φ₁.2⟩
  have hom : s₁.om (1, h) (T₁ Φ₁) = T₁ Φ' := by
    refine hOm k p ψ B.V J.W s₁.χV s₁.χW s₁.om s₁.weil _ μT hS hT _ _ F.G₀ F.G₁ T₁ hT₁ 1 1 h hk
      (isLoc_one p _) hhk Φ₁ Φ' ?_
    simp [Φ']

  obtain ⟨C, hC⟩ := exists_coreFrame p F
  obtain ⟨T₀, -, hT₀⟩ := hFl k p ν hν.1 ψ S.ψ hψ (σ + 1) B J s₁ F.s F.s_ne _ _ (c + 1 + 1) F.F₀ C F.G₀ F.F₁ F.G₁
    hC F.bes F.jac T₁ hT₁
  have hSB := ((_root_.GlobalTheory.LocFlat.flat_SB_onto k S.ψ ν S.cond.continuous hν.1 _ _ (c + 1 + 1) (σ + 1 + 1) (by omega)).1
    (by omega)).1 Φ'.1 Φ'.2
  have hflat := hT₀ Φ' ⟨_, hSB⟩ rfl
  rw [hom, hflat] at hne
  have hne' : GlobalTheory.LocFlat.flCol S.ψ ν (σ + 1 + 1) (om (S.μ (j + 1)) 1 hk ((S.T t).Phi j (c + 1 + 1) (by omega))) ≠ 0 := by
    intro h0
    apply hne
    have : (⟨_, hSB⟩ : SB _) = 0 := by
      ext1
      simpa [Φ', hΦ₁] using h0
    rw [this, map_zero]
  obtain ⟨β, q, hq, u, hu, hkeq⟩ := (hSym k ν hν s κ S t).1 j (c + 1) (by omega) (σ + 1) (by omega) hk hne'
  obtain ⟨r, hr, -⟩ := (hloc J.W _ F.G₁).1 (colE (c + 1 + 1) (σ + 1 + 1) β * q)
  obtain ⟨u', hu', -⟩ := (hloc J.W _ F.G₁).1 u
  have hprod := (hloc J.W _ F.G₁).2.2 _ _ _ _ hr hu'
  rw [← hkeq] at hprod
  obtain ⟨g', -, huniq⟩ := (hloc J.W _ F.G₁).1 hk
  refine ⟨r, hjac _ _ _ _ _ _ _ _ F.jac r β q hq hr, hr.1, u', u, hu', hu, ?_⟩
  exact (huniq _ hhk).trans (huniq _ hprod).symm

end GlobalTheory.LocMod.SuppFirst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiBesselFlatMapRowMultiplication
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

noncomputable section
open GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.MulRow

variable {D : D7}

theorem infPart_half {e : AE D} (he : IsSplitIdem D e) {z : AE D} (hz : cA D e * z = z) : infPart D z = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨β, rfl, -⟩, h3⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) = 0 := TensorProduct.zero_tmul _ _
  have he' : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have h4 : (e + cA D e) * cA D e = cA D e := by rw [add_mul, h2, he', zero_add]
  rw [← hz, ← h4, h3, map_mul, map_mul, h0, zero_mul, zero_mul]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem pr_ne {a : D.host.E} (ha : a ≠ 0) : p.pr a ≠ 0 := by
  intro h
  have h1 : p.pr a * p.pr a⁻¹ = 1 := by
    unfold Place.pr
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, map_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem pr_dot {N M : ℕ} (Q : Matrix (Fin M) (Fin N) D.host.E) (v : Fin N → D.host.E) (i : Fin M) (a : k) :
    ∑ r, p.pr (Q i r) * (a * p.pr (v r)) = a * p.pr ((Q *ᵥ v) i) := by
  unfold Place.pr
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring

theorem pr_zero : p.pr 0 = 0 := by unfold Place.pr; rw [map_zero, map_zero]

theorem pr_one : p.pr 1 = 1 := by unfold Place.pr; rw [map_one, map_one]

theorem pr_map_mul {L M N : ℕ} (X : Matrix (Fin L) (Fin M) D.host.E) (Y : Matrix (Fin M) (Fin N) D.host.E) :
    (X * Y).map p.pr = X.map p.pr * Y.map p.pr :=
  Matrix.map_mul (f := p.π.comp (incA D))

theorem hO_iso {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) (x : WO S T) (N : Mx D S₀.rank σ) :
    hO S T x (dS.ext0 T (dT.incX S₀ (adj (gA S₀ ⬝ N)))) = (N ⬝ (dT.pY ⬝ (x ⬝ dS.j0))).trace := by
  rw [dS.hO_coordS]
  simp only [HypDec.matrixExtendByZero_apply, HypDec.incX_apply, Matrix.mul_assoc, HypDec.p0_jX, HypDec.p0_j0, HypDec.p0_jY,
    Matrix.mul_one, Matrix.mul_zero, pairS, adj_zero, Matrix.zero_mul, trace_zero, zero_add, add_zero, hO_eq_trace]
  rw [adj_mul dT.jX, adj_adj, HypDec.pY_eq]
  simp only [Matrix.mul_assoc, giA_gA_cancel]

theorem qY_frame {σ : ℕ} (B : BesLev D σ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)) (hB : p.IsBesFrame B s FA FV)
    (i : Fin σ) (l : Fin c) (hl : l.val + i.val = 2 * σ) (r : n ⊕ Fin c) :
    (B.d.qY.map p.pr * FV.β) i r =
      if r = Sum.inr l then s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (σ - 1 - i.val) else 0 := by
  obtain ⟨hc, h0, hX, hz, hY⟩ := hB
  have q0 : B.d.qY * B.d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact B.d.pY_j0)
  have qX : B.d.qY * B.d.e = 0 := B.d.ee
  have qY : B.d.qY * B.d.e' = 1 := rat_injective (by rw [rat_mul, rat_one]; exact B.d.pY_jY)
  rcases r with a | j
  · rw [if_neg Sum.inl_ne_inr, Matrix.mul_apply]
    simp only [h0]
    rw [← Matrix.mul_apply, ← Matrix.mul_assoc, ← pr_map_mul, ← Matrix.mul_assoc, q0, Matrix.zero_mul,
      Matrix.map_zero _ (pr_zero p), Matrix.zero_mul, Matrix.zero_apply]
  · have hi := i.isLt
    have hj := j.isLt
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply]
    rcases lt_trichotomy j.val σ with h | h | h
    · simp only [hX ⟨j.val, h⟩ j rfl]
      rw [pr_dot p B.d.qY (fun r => B.d.e r ⟨j.val, h⟩),
        show (B.d.qY *ᵥ fun r => B.d.e r ⟨j.val, h⟩) i = (B.d.qY * B.d.e) i ⟨j.val, h⟩ from rfl, qX,
        Matrix.zero_apply, pr_zero, mul_zero, if_neg]
      intro e; cases e; omega
    · simp only [hz j h]
      rw [pr_dot p B.d.qY, Matrix.mulVec_mulVec, q0, Matrix.zero_mulVec, Pi.zero_apply, pr_zero, mul_zero, if_neg]
      intro e; cases e; omega
    · have hi' : 2 * σ - j.val < σ := by omega
      simp only [hY ⟨2 * σ - j.val, hi'⟩ j (by simp only; omega)]
      rw [pr_dot p B.d.qY (fun r => B.d.e' r ⟨_, hi'⟩),
        show (B.d.qY *ᵥ fun r => B.d.e' r ⟨_, hi'⟩) i = (B.d.qY * B.d.e') i ⟨_, hi'⟩ from rfl, qY]
      by_cases e : j = l
      · subst e
        have : i = ⟨_, hi'⟩ := Fin.ext (by simp only; omega)
        rw [← this, Matrix.one_apply_eq, pr_one, mul_one, if_pos rfl]
        congr 2
        omega
      · rw [Matrix.one_apply_ne, pr_zero, mul_zero, if_neg (fun h => e (Sum.inr_injective h))]
        intro h'
        apply e
        have := congrArg Fin.val h'
        exact Fin.ext (by simp only at this; omega)

theorem exists_row (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : k) (hs : s ≠ 0)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (hh : k)
    (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n)
    (FV : Frame k B.V.rank (n ⊕ Fin c)) (hJ : p.IsJacFrame J s hh G₀ FW) (hB : p.IsBesFrame B (s * p.xi) FA FV)
    (l : Fin c) (s' : n') (hl : σ < l.val) (b : k) : ∃ ξ : Mx D σ J.W₀.rank, (∀ i j, cA D p.e * ξ i j = ξ i j) ∧
      ∀ t, p.π (hO J.W B.V (p.up FW FV t) (J.d.ext0 B.V (B.d.incX J.W₀ ξ))) = b * t (Sum.inr l) (Sum.inl s') := by
  have hc := hB.1
  have hl' := l.isLt
  have hi : 2 * σ - l.val < σ := by omega
  have hxi : p.xi ≠ 0 := pr_ne p (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have hz : p.hz B ≠ 0 := pr_ne p B.line.2
  obtain ⟨i, hli⟩ : ∃ i : Fin σ, l.val + i.val = 2 * σ := ⟨⟨_, hi⟩, by simp only; omega⟩
  have hrow := qY_frame p B _ FA FV hB i l hli
  set u : k := s * p.xi * (-p.hz B / p.xi) * (-1 / p.xi) ^ (σ - 1 - i.val) with hu
  have hu0 : u ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hs hxi) (div_ne_zero (neg_ne_zero.2 hz) hxi))
    (pow_ne_zero _ (div_ne_zero (neg_ne_zero.2 one_ne_zero) hxi))
  have hcol : ∀ q, (FW.γ * (J.d.i₀.map p.pr * G₀.β)) q s' = if q = Sum.inl s' then 1 else 0 := fun q => by
    rw [Matrix.mul_apply]
    simp only [← hJ.2.1]
    rw [← Matrix.mul_apply, FW.γβ, Matrix.one_apply]
  have hι : ∀ x, p.e * p.ι x = p.ι x := fun x => by rw [← p.ι_π, p.π_ι]
  have hπι : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) k), (M.map p.ι).map p.π = M := fun M => by
    ext i j; exact p.π_ι _
  refine ⟨adj (gA J.W₀ ⬝ ((G₀.β * Matrix.single s' i (b / u)).map p.ι : Mx D J.W₀.rank σ)), fun i j => ?_, fun t => ?_⟩
  · simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
    rw [← map_mul, Matrix.mul_apply, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_left_comm, Matrix.map_apply, hι]
  · rw [hO_iso, AddMonoidHom.map_trace, Matrix.map_mul, hπι, Matrix.map_mul, Matrix.map_mul, Place.up, hπι]
    change ((G₀.β * Matrix.single s' i (b / u)) * (B.d.qY.map p.pr * (FV.β * t * FW.γ * J.d.i₀.map p.pr))).trace = _
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_single_mul]
    have e : B.d.qY.map p.pr * (FV.β * t * FW.γ * J.d.i₀.map p.pr) * G₀.β =
        (B.d.qY.map p.pr * FV.β) * (t * (FW.γ * (J.d.i₀.map p.pr * G₀.β))) := by simp only [Matrix.mul_assoc]
    rw [e, Matrix.mul_apply]
    simp only [hrow, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Matrix.mul_apply]
    simp only [hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_eq_mul]
    field_simp

end GlobalTheory.LocMod.MulRow


open GlobalTheory.LocMod.MulRow in
theorem GlobalTheory.LocMod.flatFB_mulrow : ∀ (D : D7), GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV → ∀ Tm, p.IsModel ψ FW FV Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l s', r = Sum.inr l ∧ σ < l.val ∧ q = Sum.inl s') → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatFB st (Tm Φ') = flatFB st (Tm Φ) := by
  intro D hFL _ k _ _ _ _ _ _ p ψ ψk hch σ J B st s hs n n' _ _ _ _ c G₀ FW FA F₀ FV hJ _ hB Tm hM r q hrq b Φ Φ' hΦ
  obtain ⟨l, s', rfl, hl, rfl⟩ := hrq
  obtain ⟨ξ, hξh, hξ⟩ := exists_row p σ J B s hs n n' c _ G₀ FW FA FV hJ hB l s' hl b
  have hy : IsHalf (cA D p.e) (J.d.ext0 B.V (B.d.incX J.W₀ ξ)) := by
    have hξ' : cA D p.e • ξ = ξ := by ext i j; exact hξh i j
    have hm : cA D p.e • ((B.d.jX ⬝ ξ) ⬝ J.d.p0) = (B.d.jX ⬝ ξ) ⬝ J.d.p0 := by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, hξ']
    intro i j
    exact congrArg (fun M => M i j) hm
  have hsym : ∀ t, ψ (symplO J.W B.V (p.up FW FV t) (J.d.ext0 B.V (B.d.incX J.W₀ ξ))) =
      (ψk (b * t (Sum.inr l) (Sum.inl s')) : ℂ) := by
    intro t
    rw [((_root_.GlobalTheory.LocSympl.halves_at_split D k p _ _ J.W B.V FW FV ψ ψk hch).2.2.2.1 t _ hy), hξ t]
  have h1 : Tm Φ' = heisO ψ J.W B.V (J.d.ext0 B.V (B.d.incX J.W₀ ξ)) (Tm Φ) := by
    refine hM.modul _ hy Φ Φ' fun t => ?_
    rw [hΦ t, hsym t]
    congr 4
    simp [basePt]
  have hmx : MxAt (fun _ => True) ξ := by
    intro i j
    refine Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (infPart_half p.split (hξh i j)), Ideal.mem_iInf.2 fun w => (w.2 trivial).elim⟩
  have hF := ((hFL ψ (fun _ => True)).2 σ J B st).Heisenberg₂
  have h0 : symplO J.W₀ B.V 0 (B.d.incX J.W₀ ξ) = 0 := by simp [symplO, hO]
  rw [h1, hF.iso (Tm Φ) (hM.theta Φ) ξ hmx, map_zero, h0, AddChar.map_zero_eq_one, one_smul]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisComb

variable {D : D7}

theorem heisO_finset_sum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) {ι : Type} (s : Finset ι)
    (a : ι → ℂ) (g : ι → WO S T → ℂ) :
    heisO ψ S T x (∑ i ∈ s, a i • g i) = ∑ i ∈ s, a i • heisO ψ S T x (g i) := by
  funext w
  simp only [heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem comb_eq_sum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c f = c.sum fun u a => a • heisO ψ S T u f := rfl

theorem comb_comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (comb ψ S T c' f) =
      ∑ x ∈ c.support, ∑ y ∈ c'.support, (c x * c' y) • heisO ψ S T x (heisO ψ S T y f) := by
  unfold comb
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [heisO_finset_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul]

theorem symplO_half (S T : HSp D) (e e' : AE D) (x y : WO S T) (he : cA D e = e) (hee : e * e' = 0)
    (hx : IsHalf e x) (hy : IsHalf e' y) : symplO S T x y = 0 := by
  have h0 : e * cA D e' = 0 := by
    conv_lhs => rw [← he]
    rw [← map_mul, hee, map_zero]
  have hh : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    rw [← hy c b, ← hx d a, map_mul]
    calc incA D (S.gram⁻¹ a b) * (cA D e' * cA D (y c b)) * incA D (T.gram c d) * (e * x d a)
        = (e * cA D e') * (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) := by ring
      _ = 0 := by rw [h0, zero_mul]
  unfold symplO
  rw [hh, mul_zero, map_zero]

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), (∀ c c' : WO S T →₀ ℂ, ∃ c'' : WO S T →₀ ℂ, (∀ w ∈ c''.support, ∃ x ∈ c.support, ∃ y ∈ c'.support, w = x + y) ∧ ∀ f, comb ψ S T c'' f = comb ψ S T c (comb ψ S T c' f)) ∧ (∀ c c' : WO S T →₀ ℂ, (∀ x ∈ c.support, ∀ y ∈ c'.support, symplO S T x y = 0) → ∀ f, comb ψ S T c (comb ψ S T c' f) = comb ψ S T c' (comb ψ S T c f)) ∧ (∀ (c : WO S T →₀ ℂ) f, IsThetaFunO ψ S T f → IsFinComb c → IsStdChar D ψ (-1) → IsThetaFunO ψ S T (comb ψ S T c f)) ∧ ∀ (e e' : AE D) (x y : WO S T), cA D e = e → e * e' = 0 → IsHalf e x → IsHalf e' y → symplO S T x y = 0 := by
  intro D ψ S T
  refine ⟨fun c c' => ?_, fun c c' h f => ?_, fun c f hf hc hψ => ?_,
    fun e e' x y he hee hx hy => symplO_half S T e e' x y he hee hx hy⟩
  · classical
    refine ⟨∑ x ∈ c.support, ∑ y ∈ c'.support, Finsupp.single (x + y) (c x * c' y * ψ (symplOH S T x y)), ?_,
      fun f => ?_⟩
    · intro w hw
      have h1 := Finsupp.support_finsetSum hw
      rw [Finset.mem_biUnion] at h1
      obtain ⟨x, hx, hw2⟩ := h1
      have h2 := Finsupp.support_finsetSum hw2
      rw [Finset.mem_biUnion] at h2
      obtain ⟨y, hy, hw3⟩ := h2
      have h3 := Finsupp.support_single_subset hw3
      rw [Finset.mem_singleton] at h3
      exact ⟨x, hx, y, hy, h3⟩
    · rw [comb_comb, comb_eq_sum]
      rw [← Finsupp.sum_finsetSum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finsupp.sum_finsetSum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finsupp.sum_single_index (zero_smul ℂ (heisO ψ S T (x + y) f)), GlobalTheory.WeilVacMove.heisO_heisO, smul_smul]
  · rw [comb_comb, comb_comb, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => ?_
    have h0 : symplOH S T x y = 0 := by
      unfold symplOH
      rw [h x hx y hy, mul_zero]
    have h1 : symplOH S T y x = 0 := by
      rw [GlobalTheory.MixModel.symplOH_skew, h0, neg_zero]
    rw [GlobalTheory.WeilVacMove.heisO_heisO, GlobalTheory.WeilVacMove.heisO_heisO, h0, h1, add_comm x y, mul_comm (c x)]
  · exact GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 f hf (WO S T) c.support id (fun u => c u) hc

end GlobalTheory.HeisComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearLawLocalModelMulClosed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

namespace GlobalTheory.LocOm.LawMul

theorem om_smul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (c : ℂ) (Φ : Matrix b a k → ℂ) :
    om μ g h (c • Φ) = c • om μ g h Φ := by
  funext x
  simp only [om, Pi.smul_apply, smul_eq_mul]
  ring

theorem lawLoc_mul : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (S T : HSp D) (ω : Om S T) (μS μT : kˣ →* ℂˣ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)) (g g' : GA D S) (gk gk' : GL Y' k) (h h' : GA D T) (hk hk' : GL Y k), LawLoc ω μS μT Tm g gk h hk → LawLoc ω μS μT Tm g' gk' h' hk' → LawLoc ω μS μT Tm (g * g') (gk * gk') (h * h') (hk * hk') := by
  intro D k _ _ _ _ S T ω μS μT Y Y' _ _ _ _ Tm g g' gk gk' h h' hk hk' H H' Φ Φ' hΦ
  let Φ₁ : SB (Matrix Y Y' k) :=
    ⟨(((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk') : ℂˣ) : ℂ) • om μS⁻¹ gk' hk' Φ.1,
      Submodule.smul_mem _ _ (GlobalTheory.SplitWeil.Model.om_mem_SB _ _ _ Φ.2)⟩
  have h1 : ω (g', h') (Tm Φ) = Tm Φ₁ := H' Φ Φ₁ rfl
  have h2 : ω (g, h) (Tm Φ₁) = Tm Φ' := by
    refine H Φ₁ Φ' ?_
    rw [hΦ, GlobalTheory.SplitWeil.Model.om_mul, map_mul, map_mul, Units.val_mul, mul_smul]
    simp only [Φ₁, om_smul]
  rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, h1, h2]

end GlobalTheory.LocOm.LawMul
end

