module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenKerOfContinuous
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainSupportOneOfPattern
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExchangeEqFiniteTranslateCombOfLevel
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
open Filter Topology

noncomputable section
namespace GlobalTheory.PosOne.UniformComb
open GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage GlobalTheory.RootEx.UniformLattices

theorem comb_sum {G ι : Type} (T : Finset ι) (g : ι → G) (a : ℂ) (f : G → ℂ) :
    comb (∑ t ∈ T, Finsupp.single (g t) a) f = a * ∑ t ∈ T, f (g t) := by
  unfold comb
  rw [← Finsupp.sum_finsetSum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finsupp.sum_single_index (zero_mul _)]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem exists_comb {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure]
    (g : (n → k) → GL (n ⊕ Fin c) k) (hg : Continuous g) (hg1 : g 0 = 1)
    (hadd : ∀ a b, g (a + b) = g a * g b) (U : Subgroup (GL (n ⊕ Fin c) k)) (hU : IsOpen (U : Set (GL (n ⊕ Fin c) k)))
    (W : Submodule 𝒪[k] (n → k)) (hW : W.IsFullLattice k) :
    ∃ e : GL (n ⊕ Fin c) k →₀ ℂ, ∀ f : GL (n ⊕ Fin c) k → ℂ,
      (∀ x b, g b ∈ U → f (g x * g b) = f (g x)) → (∀ x, x ∉ perp ψ W → f (g x) = 0) →
      ∫ x, f (g x) ∂(Measure.pi fun _ => ν) = comb e f := by
  have := secondCountable k
  have := t2Space k
  have hV : {b : n → k | g b ∈ U} ∈ 𝓝 (0 : n → k) :=
    hg.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simp [hg1, U.one_mem]))
  obtain ⟨t, ht⟩ := exists_ballLat_subset (inter_mem hV (perp_mem_nhds hψ W hW))
  have hBl : (ballLat n t).IsFullLattice k := ballLat_isLattice t
  letI : (ballLat n t).IsFullLattice k := hBl
  have hBopen := (LatPair.isClopen_lattice (ballLat n t)).2
  obtain ⟨T, hT⟩ := exists_isReps (perp ψ W) (ballLat n t).toAddSubgroup (isCompact_perp hψ hψ1 W hW) hBopen
  refine ⟨∑ x ∈ T, Finsupp.single (g x)
    ((((Measure.pi fun _ : n => ν).real ((ballLat n t).toAddSubgroup : Set (n → k)) : ℝ) : ℂ)), fun f h1 h0 => ?_⟩
  rw [comb_sum]
  refine integral_eq_sum_reps (Measure.pi fun _ : n => ν) (fun x hx => (ht hx).2)
    hBopen (isCompact_lattice _ hBl) hT (fun x => f (g x)) h0
    fun x b hb => ?_
  simp only [hadd]
  exact h1 x b (ht hb).1

end GlobalTheory.PosOne.UniformComb

namespace GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage GlobalTheory.RootEx.UniformLattices GlobalTheory.PosOne.UniformComb

theorem exchange_eq_comb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (U : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsOpen (U : Set (GL (n ⊕ Fin c) k))), ∃ e e' : GL (n ⊕ Fin c) k →₀ ℂ, ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), (∀ u ∈ U, σ u v = v) → (IsNEquiv ψ (p + 1) σ l → exDown ν p σ l v = comb e fun g => l (σ g v)) ∧ (IsNEquiv ψ p σ l → exUp ν p σ l v = comb e' fun g => l (σ g v)) := by
  intro k _ _ _ _ _ _ n _ _ c p hp hc ψ hψ hψ1 ν _ U hU
  have hrowN : {u : n → k | rowE c p u ∈ U} ∈ 𝓝 (0 : n → k) :=
    ExchangeSupport.continuous_rowE.continuousAt.preimage_mem_nhds
      (hU.mem_nhds (by simp [ExchangeSupport.rowE_zero, U.one_mem]))
  have hcolN : {β : n → k | colE c (p + 1) β ∈ U} ∈ 𝓝 (0 : n → k) :=
    ExchangeSupport.continuous_colE.continuousAt.preimage_mem_nhds
      (hU.mem_nhds (by simp [ExchangeSupport.colE_zero, U.one_mem]))
  obtain ⟨s, hs⟩ := exists_ballLat_subset hrowN
  obtain ⟨s', hs'⟩ := exists_ballLat_subset hcolN
  obtain ⟨e, he⟩ := exists_comb hψ hψ1 ν (colE c (p + 1)) ExchangeSupport.continuous_colE
    ExchangeSupport.colE_zero ExchangeSupport.colE_add U hU (ballLat n s) (ballLat_isLattice s)
  obtain ⟨e', he'⟩ := exists_comb hψ hψ1 ν (rowE c p) ExchangeSupport.continuous_rowE
    ExchangeSupport.rowE_zero ExchangeSupport.rowE_add U hU (ballLat n s') (ballLat_isLattice s')
  refine ⟨e, e', fun A _ _ σ hσ l v hv => ⟨fun hl => ?_, fun hl => ?_⟩⟩
  · refine he (fun g => l (σ g v)) (fun x b hb => ?_) (fun x hx => ?_)
    · simp only [map_mul, mul_apply_eq_comp, hv _ hb]
    · by_contra hne
      refine hx fun u hu => ?_
      have := ((ExchangeSupport.exchange_support k n c p hp hc ψ hψ hψ1 ν A σ hσ l v).2 hl).2 u x
      rw [hv _ (hs hu)] at this
      have h4 : (ψ (-(u ⬝ᵥ x)) : ℂ) = 1 := mul_right_cancel₀ hne (by rw [one_mul]; exact this.symm)
      rw [← inv_eq_one, ← AddChar.map_neg_eq_inv]
      exact Circle.ext (by simpa only [Circle.coe_one] using h4)
  · refine he' (fun g => l (σ g v)) (fun x b hb => ?_) (fun x hx => ?_)
    · simp only [map_mul, mul_apply_eq_comp, hv _ hb]
    · by_contra hne
      refine hx fun β hβ => ?_
      have := ((ExchangeSupport.exchange_support k n c p hp hc ψ hψ hψ1 ν A σ hσ l v).1 hl).2.1 x β
      rw [hv _ (hs' hβ)] at this
      have h4 : (ψ (x ⬝ᵥ β) : ℂ) = 1 := mul_right_cancel₀ hne (by rw [one_mul]; exact this.symm)
      rw [dotProduct_comm]
      exact Circle.ext (by simpa only [Circle.coe_one] using h4)

end GlobalTheory.PosOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFactorThroughFlatMapFourierJacobiColumn
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.LocFlat

section Lin
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}


open Classical in
theorem flCol_integrand_integrable (ψ : AddChar k Circle) (hψ : Continuous ψ) (ν : Measure k)
    (hν : ν.IsAddHaarMeasure) (p : ℕ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (x : Matrix n (n' ⊕ Unit) k) :
    Integrable (fun e => Φ (ptCol p x e) * (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ))
      (Measure.pi fun _ => ν) := by
  have := GlobalTheory.SplitWeil.t2Space k
  have := GlobalTheory.SplitWeil.secondCountable k
  have := hν
  have hemb : Topology.IsClosedEmbedding (fun e => ptCol (c := c) p x e) := by
    have hslice : Topology.IsClosedEmbedding (Prod.mk x.toCols₁ :
        ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → _) :=
      Function.LeftInverse.isClosedEmbedding (f := Prod.snd) (fun _ => rfl)
        continuous_snd (Continuous.prodMk_right x.toCols₁)
    exact (Homeomorph.addRight (colAt n' c p fun r => x r (Sum.inr ()))).isClosedEmbedding.comp
      ((isClosedEmbedding_affPt_uncurry p).comp hslice)
  have hch : Continuous fun e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k =>
      ((ψ (-ch (affPt p (0 : Matrix n n' k) e)) : Circle) : ℂ) := by
    refine continuous_subtype_val.comp (hψ.comp (Continuous.neg ?_))
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_affPt_uncurry p).comp (Continuous.prodMk_right (0 : Matrix n n' k))).matrix_elem _ _
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (hΦ.1.continuous.comp hemb.continuous).mul hch
  · exact (hΦ.2.comp_isClosedEmbedding hemb).mul_right

theorem flCol_add_of_SB (ψ : AddChar k Circle) (hψ : Continuous ψ) (ν : Measure k)
    (hν : ν.IsAddHaarMeasure) (p : ℕ) (Φ₁ Φ₂ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (h₁ : Φ₁ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (h₂ : Φ₂ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    flCol ψ ν p (Φ₁ + Φ₂) = flCol ψ ν p Φ₁ + flCol ψ ν p Φ₂ := by
  funext x
  simp only [flCol_eq_integral, Pi.add_apply, add_mul]
  exact integral_add (flCol_integrand_integrable ψ hψ ν hν p Φ₁ h₁ x)
    (flCol_integrand_integrable ψ hψ ν hν p Φ₂ h₂ x)

theorem flCol_smul (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (a : ℂ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) :
    flCol ψ ν p (a • Φ) = a • flCol ψ ν p Φ := by
  funext x
  simp only [flCol_eq_integral, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

end Lin

theorem flCol_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c + 1 → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), (∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), (∀ x, GlobalTheory.LocFlat.flCol ψ ν p Φ.1 x = 0) → L Φ = 0) → ∃ L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψ ν p Φ.1 → L Φ = L₀ Ψ := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p hp1 hpc M _ _ L hL
  have hSB := (flat_SB_onto k ψ ν hψ hν n n' c p hp1).1 hpc
  let F : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) :=
    { toFun := fun Φ => ⟨flCol ψ ν p Φ.1, hSB.1 Φ.1 Φ.2⟩
      map_add' := fun Φ₁ Φ₂ => Subtype.ext (flCol_add_of_SB ψ hψ ν hν p Φ₁.1 Φ₂.1 Φ₁.2 Φ₂.2)
      map_smul' := fun a Φ => Subtype.ext (flCol_smul ψ ν p a Φ.1) }
  have hFs : Function.Surjective F := fun Ψ => by
    obtain ⟨Φ, hΦ, h⟩ := hSB.2 Ψ.1 Ψ.2
    exact ⟨⟨Φ, hΦ⟩, Subtype.ext h⟩
  have hker : LinearMap.ker F ≤ LinearMap.ker L := fun Φ hΦ => by
    rw [LinearMap.mem_ker] at hΦ ⊢
    apply hL
    intro x
    have := congrArg (fun Ψ : SB (Matrix n (n' ⊕ Unit) k) => Ψ.1 x) hΦ
    simpa [F] using this
  refine ⟨((LinearMap.ker F).liftQ L hker).comp (F.quotKerEquivOfSurjective hFs).symm.toLinearMap, ?_⟩
  intro Φ Ψ hΨ
  have hΨF : Ψ = F Φ := Subtype.ext hΨ
  subst hΨF
  have h2 : (F.quotKerEquivOfSurjective hFs).symm (F Φ) = Submodule.Quotient.mk Φ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h2]
  rfl

end GlobalTheory.LocFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymDataOfUnifCongr
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymChain
namespace UnifChange
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

section General
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']

theorem apply_mul_KOne {f : Matrix ι ι' k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x) (hp : ∀ x y, MaxM y → f (x + y) = f x)
    {a : GL ι k} (ha : a ∈ KOne k ι) {b : GL ι' k} (hb : b ∈ KOne k ι') (x : Matrix ι ι' k) :
    f (a.val * x * b.val) = f x := by
  obtain ⟨a1, a2⟩ := mem_KO.1 (KOne_le_KO ha)
  obtain ⟨b1, b2⟩ := mem_KO.1 (KOne_le_KO hb)
  by_cases hx : IntM x
  · have e : a.val * x * b.val = x + ((a.val - 1) * x * b.val + x * (b.val - 1)) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]; abel
    rw [e]
    exact hp _ _ ((((mem_KOne.1 ha).mul_intM hx).mul_intM b1).add (hx.mul_maxM (mem_KOne.1 hb)))
  · have h1 : f x = 0 := by_contra fun h => hx (hs _ h)
    rw [h1]
    by_contra h
    have := (a2.mul (hs _ h)).mul b2
    apply hx
    simpa [Matrix.mul_assoc, ← Matrix.mul_assoc (a⁻¹).val] using this

theorem reGL_symm_mem_KOne (e : ι ≃ Y) {d : GL Y k} (hd : d ∈ KOne k Y) : (reGL e).symm d ∈ KOne k ι :=
  mem_KOne.2 fun i j => by simpa [reGL_symm_val, Matrix.one_apply] using mem_KOne.1 hd (e i) (e j)

def Near (F G : LatFrame (k := k) (ι := ι) (Y := Y)) : Prop :=
  G.ord = F.ord ∧ F.bas⁻¹ * G.bas ∈ KOne k Y

theorem Near.conj {F G : LatFrame (k := k) (ι := ι) (Y := Y)} (h : Near F G) :
    ∃ d ∈ KOne k ι, ∀ g, G.conj.symm g = d⁻¹ * F.conj.symm g * d := by
  refine ⟨_, reGL_symm_mem_KOne F.ord h.2, fun g => ?_⟩
  rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply, h.1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have : reGL F.ord (F.conj.symm g) = F.bas⁻¹ * g * F.bas := by
    conv_rhs => rw [← F.conj.apply_symm_apply g, LatFrame.conj_apply]
    group
  rw [this]; group

theorem Near.J_eq {F G : LatFrame (k := k) (ι := ι) (Y := Y)} (h : Near F G)
    (P : TypeDatum (k := k) (a := ι)) :
    (P.toLevel.map G.conj).J = (P.toLevel.map F.conj).J := by
  obtain ⟨d, hd, e⟩ := h.conj
  ext g
  rw [Level.mem_map, Level.mem_map, e, P.J.mul_mem_cancel_right (P.KOne_le hd),
    P.J.mul_mem_cancel_left (inv_mem (P.KOne_le hd))]

theorem Near.stabLat_eq {F G : LatFrame (k := k) (ι := ι) (Y := Y)} (h : Near F G) :
    stabLat G.bas = stabLat F.bas := by
  ext g
  have hd := KOne_le_KO h.2
  have e : G.bas⁻¹ * g * G.bas = (F.bas⁻¹ * G.bas)⁻¹ * (F.bas⁻¹ * g * F.bas) * (F.bas⁻¹ * G.bas) := by group
  rw [mem_stabLat, mem_stabLat, e, (KO k Y).mul_mem_cancel_right hd, (KO k Y).mul_mem_cancel_left (inv_mem hd)]

theorem Near.transport_eq {F G : LatFrame (k := k) (ι := ι) (Y := Y)}
    {F' G' : LatFrame (k := k) (ι := ι') (Y := Y')} (h : Near F G) (h' : Near F' G')
    {f : Matrix ι ι' k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x) (hp : ∀ x y, MaxM y → f (x + y) = f x) :
    G.transport G' f = F.transport F' f := by
  funext x
  change f (G.coords G' x) = f (F.coords F' x)
  rw [← apply_mul_KOne hs hp (reGL_symm_mem_KOne F.ord (inv_mem h.2)) (reGL_symm_mem_KOne F'.ord h'.2) (F.coords F' x)]
  congr 1
  unfold LatFrame.coords
  rw [reGL_symm_val, reGL_symm_val, submatrix_mul_equiv, submatrix_mul_equiv, h.1, h'.1]
  congr 1
  simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.bas.val, Units.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc F'.bas.val, Units.mul_inv,
    Matrix.one_mul]

theorem near_refl (F : LatFrame (k := k) (ι := ι) (Y := Y)) : Near F F := ⟨rfl, by simp⟩

theorem val_pow_sub_one {u : k} (hu : valuation k (u - 1) < 1) (m : ℕ) : valuation k (u ^ m - 1) < 1 := by
  have h1 : valuation k u ≤ 1 := by
    have := Valuation.map_add_le (valuation k) hu.le (le_of_eq (map_one (valuation k)))
    simpa using this
  induction m with
  | zero => simp
  | succ m ih =>
    have e : u ^ (m + 1) - 1 = u * (u ^ m - 1) + (u - 1) := by ring
    rw [e]
    refine Valuation.map_add_lt _ ?_ hu
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right h1 zero_le ih

variable {ϖ ϖ' : kˣ}

theorem val_div_sub_one (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) :
    valuation k ((ϖ : k)⁻¹ * ϖ' - 1) < 1 := by
  have e : (ϖ : k)⁻¹ * ϖ' - 1 = (ϖ : k)⁻¹ * ((ϖ' : k) - ϖ) := by field_simp
  have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
  rwa [e, map_mul, map_inv₀, inv_mul_lt_one₀ h0]

theorem near_typeFrame {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) (o : ι ≃ n ⊕ Fin c) :
    Near (typeFrame ϖ o) (typeFrame ϖ' o) := by
  have frameVal (u : kˣ) : (typeFrame u o).bas.val =
      diagonal (Sum.elim (fun _ => 1) fun i : Fin c => (u : k) ^ (i.val + 1)) := by
    change fromBlocks 1 0 0 (diagonal _) = _
    rw [← fromBlocks_diagonal]
    simp
  have frameInvVal : ((typeFrame ϖ o).bas⁻¹).val =
      diagonal (Sum.elim (fun _ => 1) fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [frameVal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rcases i with i | i <;> simp
  refine ⟨rfl, mem_KOne.2 fun i j => ?_⟩
  rw [Units.val_mul, frameInvVal, frameVal, diagonal_mul_diagonal, ← diagonal_one, diagonal_sub, diagonal_apply]
  split_ifs
  · rcases i with i | i
    · simp
    · have := val_pow_sub_one (val_div_sub_one h) (i.val + 1)
      rwa [mul_pow, inv_pow] at this
  · simp

theorem val_eq (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) :
    valuation k (ϖ' : k) = valuation k (ϖ : k) := Valuation.map_eq_of_sub_lt _ h

theorem isUnif_of_near (hϖ : IsUnif ϖ) (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) : IsUnif ϖ' :=
  fun x => by rw [val_eq h]; exact hϖ x

theorem inv_sub_inv_mem (hϖ : IsUnif ϖ) (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) :
    valuation k (((ϖ'⁻¹ : kˣ) : k) - ((ϖ⁻¹ : kˣ) : k)) ≤ 1 := by
  have h1 := (hϖ _).1 (val_div_sub_one h)
  have e : ((ϖ'⁻¹ : kˣ) : k) - ((ϖ⁻¹ : kˣ) : k) = -((ϖ' : k)⁻¹ * ((ϖ : k)⁻¹ * ϖ' - 1)) := by
    simp only [Units.val_inv_eq_inv_val]; field_simp; ring
  have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
  rwa [e, Valuation.map_neg, map_mul, map_inv₀, val_eq h, inv_mul_le_one₀ h0]

theorem psi_inv_mul {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (hϖ : IsUnif ϖ)
    (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) {x : k} (hx : x ∈ 𝒪[k]) :
    ψ ((ϖ'⁻¹ : kˣ) * x) = ψ ((ϖ⁻¹ : kˣ) * x) := by
  have hi : (((ϖ'⁻¹ : kˣ) : k) - ((ϖ⁻¹ : kˣ) : k)) * x ∈ 𝒪[k] := mul_mem (inv_sub_inv_mem hϖ h) hx
  have e : ((ϖ'⁻¹ : kˣ) : k) * x = (ϖ⁻¹ : kˣ) * x + (((ϖ'⁻¹ : kˣ) : k) - ((ϖ⁻¹ : kˣ) : k)) * x := by ring
  rw [e, AddChar.map_add_eq_mul, hψ.eq_one (show _ ∈ cball (1 : kˣ) from hi), mul_one]

theorem isSymLevel_of_near {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (hϖ : IsUnif ϖ)
    (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) {ρ κ l : ℕ}
    {P : TypeDatum (k := k) (a := Fin κ ⊕ Fin l)}
    (hP : IsSymLevel ψ ϖ ρ P) : IsSymLevel ψ ϖ' ρ P := by
  refine ⟨hP.1, fun g => ?_⟩
  have hg := intM_of_mem_KO (P.le_KO g.2)
  rw [hP.2 g, psi_inv_mul hψ hϖ h, psi_inv_mul hψ hϖ h]
  · refine sum_mem fun r _ => sum_mem fun s _ => ?_
    split_ifs
    exacts [hg _ _, zero_mem _]
  · unfold simpleSum
    refine sum_mem fun r _ => sum_mem fun s _ => ?_
    split_ifs
    exacts [hg _ _, zero_mem _]

variable {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]

theorem transport_iterPhi (P : TypeDatum (k := k) (a := r)) (μ : ℕ → kˣ →* ℂˣ)
    (hμ : ∀ j, IsTame (μ j)) (j : ℕ)
    {F G : LatFrame (k := k) (ι := Ix r t (j + 1)) (Y := Y)}
    {F' G' : LatFrame (k := k) (ι := Ix r t j) (Y := Y')} (h : Near F G) (h' : Near F' G') :
    G.transport G' (P.iterPhi t μ hμ j) = F.transport F' (P.iterPhi t μ hμ j) :=
  h.transport_eq h'
    (fun x hx i l => by simpa using TypeDatum.intM_of_Phi_ne_zero _ _ hx ((ixSucc r t j).symm i) l)
    fun x y hy => TypeDatum.Phi_add _ (hμ _) (x.submatrix (ixSucc r t j) id) (y := y.submatrix (ixSucc r t j) id)
      fun _ _ => hy _ _

end General
end UnifChange

open UnifChange

theorem exists_symData_of_unif_congr : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {s κ : ℕ} (S : SymData k s κ) (ϖ' : kˣ), valuation k ((ϖ' : k) - (S.ϖ : k)) < valuation k (S.ϖ : k) → ∃ S' : SymData k s κ, S'.ϖ = ϖ' ∧ S'.ψ = S.ψ ∧ S'.ρ = S.ρ ∧ S'.P = S.P ∧ S'.μ = S.μ ∧ ∀ (τ : ℕ) (ν : Measure k), (∀ j c h, (S'.T (Fin τ)).Phi j c h = (S.T (Fin τ)).Phi j c h) ∧ (∀ j c h, (S'.T (Fin τ)).entry S'.ψ ν j c h 1 1 = (S.T (Fin τ)).entry S.ψ ν j c h 1 1) ∧ (∀ x₀, (S'.T (Fin τ)).Psi 1 x₀ (S'.y0 (Fin τ)) = (S.T (Fin τ)).Psi 1 x₀ (S.y0 (Fin τ))) ∧ (S'.T (Fin τ)).xiTop (box _ (1 : kˣ)) S'.ψ ν (-1) (Submodule.Quotient.mk (S'.y0 (Fin τ))) = (S.T (Fin τ)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin τ))) := by
  intro k _ _ _ _ _ _ s κ S ϖ' h
  let S' : SymData k s κ :=
    { S with ϖ := ϖ', unif := isUnif_of_near S.unif h, sym := isSymLevel_of_near S.cond S.unif h S.sym }
  refine ⟨S', rfl, rfl, rfl, rfl, rfl, fun τ ν => ?_⟩
  have hPhi : ∀ j c H, (S'.T (Fin τ)).Phi j c H = (S.T (Fin τ)).Phi j c H := fun j c H =>
    transport_iterPhi S.P S.μ S.tame j (near_typeFrame h _) (near_typeFrame h _)
  have hTop : (S'.T (Fin τ)).PhiTop = (S.T (Fin τ)).PhiTop :=
    transport_iterPhi S.P S.μ S.tame (s + 1) (near_refl _) (near_typeFrame h _)
  have hJ : ∀ j c H, ((S'.T (Fin τ)).lev j c H).J = ((S.T (Fin τ)).lev j c H).J := fun j c H =>
    (near_typeFrame h _).J_eq _
  have hB : ∀ j c (H : j + c = s + 1), stabLat ((S'.T (Fin τ)).bas j c H) = stabLat ((S.T (Fin τ)).bas j c H) := fun j c H =>
    (near_typeFrame h (stdOrd (Fin κ) (Fin τ) j c H)).stabLat_eq
  have hy : S'.y0 (Fin τ) - S.y0 (Fin τ) ∈ box (XIx (Fin κ) (Fin τ) (s + 1)) (1 : kˣ) := by
    intro i
    unfold SymData.y0
    rw [← Pi.single_sub, Pi.single_apply]
    split_ifs
    · simpa using inv_sub_inv_mem S.unif h
    · simp
  refine ⟨hPhi, fun j c H => ?_, fun x₀ => ?_, ?_⟩
  · unfold Chain.entry xi volNat
    rw [hPhi, hJ, hB]
    rfl
  · let t := Fin τ
    let rowOrd := stdOrd (Fin κ) t (s + 1) 0 rfl
    let colOrd := stdOrd (Fin κ) t s (0 + 1) rfl
    have coords (u : kˣ) (y : XIx (Fin κ) t (s + 1) → k) :
        (typeFrame u rowOrd).coords (typeFrame u colOrd) (withCol x₀ y) =
          (withCol x₀ ((u : k) • y)).submatrix rowOrd colOrd := by
      have rowBas : (typeFrame u rowOrd).bas = 1 := by
        apply Units.ext
        ext i j
        rcases i with i | i
        · rcases j with j | j
          · simp [typeFrame, embA, Matrix.one_apply]
          · exact j.elim0
        · exact i.elim0
      unfold LatFrame.coords
      rw [rowBas]
      congr 1
      ext i j
      rcases i with i | i
      · rcases j with j | j
        · simp [withCol, typeFrame, embA, Matrix.fromBlocks_multiply]
        · simp [withCol, typeFrame, embA, Matrix.fromBlocks_multiply, Fin.eq_zero j, mul_comm]
      · exact i.elim0
    have scaled : (ϖ' : k) • S'.y0 t = (S.ϖ : k) • S.y0 t := by
      ext i
      simp only [SymData.y0, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs <;> simp [S']
    simp only [Chain.Psi, om_one, SymData.T, typeChain, Chain.ofType, LatFrame.transport]
    rw [coords ϖ', coords S.ϖ, scaled]
  · unfold Chain.xiTop
    rw [hTop, (Submodule.Quotient.eq _).2 hy]

end GlobalTheory.SymChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatColumnSupportOfOneIndexAtSymPosition
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LocFlat.SuppColProof

theorem det_colE {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (β : n → k) :
    Matrix.GeneralLinearGroup.det (colE c p β) = 1 := by
  ext
  simp [colE, upU]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem om_colE {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (μ : kˣ →* ℂˣ) (g h : GL (n ⊕ Fin c) k) (hg : Matrix.GeneralLinearGroup.det g = 1)
    (Φ : Matrix (n ⊕ Fin c) n' k → ℂ) :
    (fun z => om μ 1 h Φ (g.val * z)) = om μ 1 (g⁻¹ * h) Φ := by
  rw [show om μ 1 (g⁻¹ * h) Φ = om μ (1 * 1) (g⁻¹ * h) Φ by rw [mul_one], om_mul]
  funext z
  have hi : Matrix.GeneralLinearGroup.det g⁻¹ = 1 := by rw [map_inv, hg, inv_one]
  simp [om, hi, nabs_one]

end GlobalTheory.LocFlat.SuppColProof


open GlobalTheory.LocFlat.SuppColProof in
theorem GlobalTheory.LocFlat.suppCol_of_oneIndexAt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.OneIndexAt t ν → GlobalTheory.LocFlat.SuppCol S t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hOne j c H r hr h hne
  have hΦ : (S.T t).Phi j (c + 1) (by omega) ∈ SB _ :=
    (Chain.ofType_regular _ _ _ _ _).1 j (c + 1) (by omega)
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
  rw [_root_.GlobalTheory.LocFlat.flCol_eq_opE_colE k S.ψ ν S.cond.continuous hν.1 _ _ (c + 1) (r + 1) (by omega) (by omega) _
    (om_mem_SB _ 1 h hΦ) x] at hx
  have hf := om_colE (n' := XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) (S.μ (j + 1))
    (colE (c + 1) (r + 1) fun a => x a (Sum.inr ())) h (det_colE _ _ _) ((S.T t).Phi j (c + 1) (by omega))
  have hx' : opE S.ψ ν (r + 1) (om (S.μ (j + 1)) 1 ((colE (c + 1) (r + 1) fun a => x a (Sum.inr ()))⁻¹ * h)
      ((S.T t).Phi j (c + 1) (by omega))) x.toCols₁ ≠ 0 := by
    rw [← hf]; exact hx
  obtain ⟨q, hq, u, hu, e⟩ := hOne j (c + 1) (by omega) (r + 1) (by omega) (by omega) _ (fun hz => hx' (by rw [hz]; rfl))
  refine ⟨fun a => x a (Sum.inr ()), q, hq, u, hu, ?_⟩
  rw [mul_assoc, ← e, mul_inv_cancel_left]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumHeckeSeriesSphericalIntegralInverseStatement
section
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_hecke_series_spherical_integral_inverse : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ X : ℂ, (∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X‖ < 1) → HasSum (fun c : {c : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k])} => X ^ (-ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ c.1.out) (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) := by
  first | exact @GlobalTheory.HeckeDual.hasSum_dual | exact GlobalTheory.HeckeDual.hasSum_dual | (intros; apply GlobalTheory.HeckeDual.hasSum_dual <;> assumption)
end

