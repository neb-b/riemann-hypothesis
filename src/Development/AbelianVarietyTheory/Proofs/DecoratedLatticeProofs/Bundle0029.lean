module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0027

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiRowAdd
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.LocFlat

theorem add_right_mem_SB {m m' k : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k]
    {Φ : Matrix m m' k → ℂ} (hΦ : Φ ∈ SB (Matrix m m' k)) (a : Matrix m m' k) :
    (fun z => Φ (z + a)) ∈ SB (Matrix m m' k) :=
  ⟨hΦ.1.comp_continuous (continuous_add_const a), hΦ.2.comp_homeomorph (Homeomorph.addRight a)⟩

theorem flRow_add : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (Φ₁ Φ₂ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), Φ₁ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) → Φ₂ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) → GlobalTheory.LocFlat.flRow ψ ν p (Φ₁ + Φ₂) = GlobalTheory.LocFlat.flRow ψ ν p Φ₁ + GlobalTheory.LocFlat.flRow ψ ν p Φ₂ := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p Φ₁ Φ₂ h₁ h₂
  funext x
  have H := opE_smul_add p hψ ν (1 : ℂ)
    (add_right_mem_SB h₁ (rowAt n c p (x (Sum.inr ()))))
    (add_right_mem_SB h₂ (rowAt n c p (x (Sum.inr ()))))
  have H' := congrFun H x.toRows₁
  simp only [one_smul, Pi.add_apply] at H'
  simp only [flRow, Pi.add_apply]
  rw [← H']
  rfl

end GlobalTheory.LocFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatRowIndicatorOfSymLevelExchange
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LocFlat

theorem lam_rowE_symLevel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t],
    ∀ j c (H : j + 1 + c = s) (r : ℕ), c = 2 * r → ∀ u : XIx (Fin κ) t j → k,
      ∀ hm : rowE (c + 1 + 1) (r + 1) u ∈ ((S.T t).lev j (c + 1 + 1) (by omega)).J,
      ((S.T t).lev j (c + 1 + 1) (by omega)).lam ⟨_, hm⟩ = 1 := by
  intro k _ _ _ _ s κ S t _ _ j c H r hc u hm
  have hodd := S.odd
  have hsh := _root_.GlobalTheory.typeFrame_conj_symm_rowE_apply k (Fin κ) t S.ϖ j (c + 1 + 1) (s + 1) (by omega) r (by omega) u
  obtain ⟨g, hg, hl⟩ := GlobalTheory.T.iteratedDepthOneLevel_char_of_one_row_first_block k _ t S.P S.μ S.tame j (Sum.inr ⟨r, by omega⟩) ⟨_, hm⟩
    (fun a b ha => by
      have := hsh a b
      rw [if_neg ha, add_zero] at this
      exact this)
    (by
      have := hsh (Sum.inl (Sum.inr ⟨r, by omega⟩)) (Sum.inl (Sum.inr ⟨r, by omega⟩))
      rw [if_pos rfl] at this
      have e := standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1 + 1) (l := s + 1) (by omega) ⟨r, by omega⟩
      simp only at e
      rw [e] at this
      simpa using this)
  have hsym : S.P.lam g = 1 := by
    refine GlobalTheory.T.symmetricPositionLevel_character_eq_one_single_row k S.ψ S.ϖ S.ρ κ (s + 1) S.P S.sym ⟨r, by omega⟩ g (fun a b ha => ?_) (fun i hi => ?_)
    · rw [hg, submatrix_apply]
      have := hsh (Sum.inl a) (Sum.inl b)
      rw [if_neg (fun e => ha (Sum.inl_injective e)), add_zero] at this
      exact this.trans (by simp [Matrix.one_apply])
    · have ei : i = ⟨r + 1, by omega⟩ := Fin.ext hi
      rw [hg, submatrix_apply, ei]
      have := hsh (Sum.inl (Sum.inr ⟨r, by omega⟩)) (Sum.inl (Sum.inr ⟨r + 1, by omega⟩))
      rw [if_pos rfl] at this
      have e := standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1 + 1) (l := s + 1) (by omega) ⟨r + 1, by omega⟩
      simp only at e
      rw [e] at this
      exact this.trans (by simp [Matrix.one_apply])
  exact hl.trans hsym

theorem pureRow_of_exchange : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type)
    [Fintype t] [DecidableEq t], S.Pattern t → S.ExchangeAt t ν → GlobalTheory.LocFlat.PureRow S t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hP hE
  haveI := hν.1
  intro j c H r hc
  have hodd := S.odd
  obtain ⟨C, hC, hEq⟩ := hE j (c + 1) (by omega) (r + 1) (by omega) (by omega) (by omega)
  have HR : (S.T t).Regular := Chain.ofType_regular _ _ _ _ _
  have HL : (S.T t).Laws := Chain.ofType_laws _ _ _ _ _
  set Φ := (S.T t).Phi j (c + 1) (by omega) with hΦ
  set V := volNat ν ((S.T t).bas (j + 1) (c + 1) (by omega)) (Cgrp ((S.T t).lev (j + 1) (c + 1) (by omega)).J 1)
    with hV
  have hVpos : 0 < V :=
    volNat_Cgrp_pos ν (HR.2.2 (j + 1) (c + 1) (by omega)).1 (HR.2.2 (j + 1) (c + 1) (by omega)).2.1 _ 1
  have hom1 : om ((S.T t).mu (j + 1)) 1 1 Φ = Φ := by
    funext z; simp [om, nabs]
  have hentry : ∀ x₀, (S.T t).entry S.ψ ν j c H 1 1 x₀ = ((V⁻¹ : ℝ) : ℂ) * opE S.ψ ν 1 Φ x₀ := by
    intro x₀
    simp only [Chain.entry, xi, flat]
    rw [hom1]
  refine ⟨C * V, mul_pos hC hVpos, fun x => ?_⟩
  by_cases hu : x (Sum.inr ()) ∈ box (XIx (Fin κ) t j) (S.ϖ ^ (r + 1))
  · rw [if_pos hu, mul_one, hentry]
    have hm := _root_.GlobalTheory.SymChain.rowE_mem_symLev_of_box k s κ S t hP j c H r hc _ hu
    have hl := lam_rowE_symLevel k s κ S t j c H r hc _ hm
    have hdet : Matrix.GeneralLinearGroup.det (rowE (c + 1 + 1) (r + 1) (x (Sum.inr ()))) = 1 := by
      ext; simp [rowE, lowU, Matrix.det_fromBlocks_zero₁₂]
    have hT := (HL.1 j (c + 1) (by omega)).1 ⟨_, hm⟩
    rw [hl] at hT
    have hfun : (fun z => Φ (z * (rowE (c + 1 + 1) (r + 1) (x (Sum.inr ()))).val)) = Φ := by
      funext z
      have := congrFun hT z
      simpa [om, hdet, nabs] using this
    rw [_root_.GlobalTheory.LocFlat.flRow_eq_opE_rowE k S.ψ ν S.cond.continuous inferInstance (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (c + 1)
      (r + 1) (by omega) (by omega) Φ (HR.1 j (c + 1) (by omega)) x]
    erw [hfun]
    rw [congrFun hEq]
    have hV0 : (V : ℂ) ≠ 0 := by exact_mod_cast hVpos.ne'
    rw [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
    field_simp
  · rw [if_neg hu, mul_zero, _root_.GlobalTheory.LocFlat.flRow_eq_zero_of_not_mem_box k ν s κ S t j c H r hc x hu]

end GlobalTheory.LocFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCoordinateShearHaarLocalField
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.CoordShear

theorem measurePreserving_shear {k : Type} [AddCommGroup k] [MeasurableSpace k] [MeasurableAdd₂ k]
    (ν : Measure k) [SigmaFinite ν] [ν.IsAddLeftInvariant]
    {J : Type} [Fintype J] [DecidableEq J] (S : Finset J) (g : (J → k) → (J → k))
    (hg : Measurable g) (h1 : ∀ y y' : J → k, (∀ j, j ∉ S → y j = y' j) → g y = g y')
    (h2 : ∀ (y : J → k) j, j ∉ S → g y j = 0) :
    MeasurePreserving (fun y => y + g y) (Measure.pi fun _ : J => ν) (Measure.pi fun _ : J => ν) := by
  classical
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : J => k) (fun j => j ∉ S) with he
  have he_mp : MeasurePreserving e (Measure.pi fun _ : J => ν)
      ((Measure.pi fun _ : {j // j ∉ S} => ν).prod (Measure.pi fun _ : {j // ¬ j ∉ S} => ν)) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : J => ν) (fun j => j ∉ S)
  let G : ({j // j ∉ S} → k) → ({j // ¬ j ∉ S} → k) := fun b i => g (e.symm (b, 0)) i
  have hG : Measurable G := by
    refine Measurable.of_eval fun i => ?_
    exact (measurable_pi_apply (i : J)).comp
      (hg.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const)))
  have hΦ : MeasurePreserving
      (fun p : ({j // j ∉ S} → k) × ({j // ¬ j ∉ S} → k) => (id p.1, G p.1 + p.2))
      ((Measure.pi fun _ : {j // j ∉ S} => ν).prod (Measure.pi fun _ : {j // ¬ j ∉ S} => ν))
      ((Measure.pi fun _ : {j // j ∉ S} => ν).prod (Measure.pi fun _ : {j // ¬ j ∉ S} => ν)) := by
    refine (MeasurePreserving.id _).skew_product (g := fun b a => G b + a) ?_ ?_
    · exact (hG.comp measurable_fst).add measurable_snd
    · exact Filter.Eventually.of_forall fun b => (measurePreserving_add_left _ (G b)).map_eq

  have hGy : ∀ y : J → k, g (e.symm ((e y).1, 0)) = g y := by
    intro y
    refine h1 _ _ fun j hj => ?_
    simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hj]
  have key : (fun y => y + g y) = e.symm ∘ (fun p => (id p.1, G p.1 + p.2)) ∘ e := by
    funext y
    apply e.injective
    rw [Function.comp_apply, Function.comp_apply, MeasurableEquiv.apply_symm_apply]
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, h2 y i i.2]
    · have := congrFun (hGy y) i
      simp only [G, Pi.add_apply]
      rw [this]
      simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, add_comm]
  rw [key]
  exact (MeasurePreserving.symm e he_mp).comp (hΦ.comp he_mp)

theorem integral_shear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (J : Type) [Fintype J] [DecidableEq J] (S : Finset J) (g : (J → k) → (J → k)), Continuous g → (∀ y y' : J → k, (∀ j, j ∉ S → y j = y' j) → g y = g y') → (∀ (y : J → k) j, j ∉ S → g y j = 0) → ∀ F : (J → k) → ℂ, ∫ y, F (y + g y) ∂(Measure.pi fun _ => ν) = ∫ y, F y ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ ν hν J _ _ S g hg h1 h2 F

  have : SecondCountableTopology k := by
    let := IsTopologicalAddGroup.rightUniformSpace k
    have := isUniformAddGroup_of_addCommGroup (G := k)
    let : (Valued.v (R := k)).RankOne :=
      { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    let : NontriviallyNormedField k := Valued.toNontriviallyNormedField k (ValueGroupWithZero k)
    have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
    exact secondCountable_of_proper
  have := hν
  have hgm : Measurable g := hg.measurable
  have hmp := measurePreserving_shear ν S g hgm h1 h2
  have hfix : ∀ y, g (y + g y) = g y := fun y => h1 _ _ fun j hj => by simp [h2 y j hj]
  have hfix' : ∀ y, g (y - g y) = g y := fun y => h1 _ _ fun j hj => by simp [h2 y j hj]
  have hsurj : Function.Surjective (fun y : J → k => y + g y) :=
    fun y => ⟨y - g y, by simp [hfix']⟩
  have hemb : MeasurableEmbedding (fun y : J → k => y + g y) :=
    MeasurableEmbedding.of_measurable_inverse (g := fun y => y - g y) (measurable_id.add hgm)
      (by rw [hsurj.range_eq]; exact MeasurableSet.univ) (measurable_id.sub hgm)
      (fun y => by simp [hfix])
  exact hmp.integral_comp hemb F

end GlobalTheory.CoordShear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsQuotientInvariantIntegralExchangeToPositionOne
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

noncomputable section
namespace GlobalTheory.PosOneIntegral

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def omRight (μ : kˣ →* ℂˣ) : Representation ℂ (GL n k) (SB (Matrix n n' k)) where
  toFun g :=
    { toFun := fun Ψ => ⟨om μ (1 : GL n' k) g Ψ.1, om_mem_SB μ 1 g Ψ.2⟩
      map_add' := fun Φ Ψ => by
        apply Subtype.ext
        funext x
        simp only [om, Submodule.coe_add, Pi.add_apply]
        ring
      map_smul' := fun z Φ => by
        apply Subtype.ext
        funext x
        simp only [om, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  map_one' := by
    apply LinearMap.ext
    intro Ψ
    apply Subtype.ext
    exact om_one μ Ψ.1
  map_mul' g h := by
    apply LinearMap.ext
    intro Ψ
    apply Subtype.ext
    show om μ (1 : GL n' k) (g * h) Ψ.1 = om μ 1 g (om μ 1 h Ψ.1)
    rw [← om_mul μ 1 1 g h Ψ.1, mul_one]

variable {c : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]

theorem bilPos_iff_isPos (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (p : ℕ)
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) :
    BilPos ψ μ p σ B ↔ IsPos ψ p (omRight μ) σ B := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun g Ψ v => h2 g Ψ _ v rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun g Ψ Ψ₁ v hΨ => ?_⟩
    have : Ψ₁ = omRight μ g Ψ := Subtype.ext hΨ
    rw [this]
    exact h2 g Ψ v

end GlobalTheory.PosOneIntegral
end

open GlobalTheory.PosOneIntegral in
theorem GlobalTheory.PosOneIntegral.positionOne_invariantIntegral_exchange_step (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k) (hν : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (hμ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (hσ : IsSmoothRep σ) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (hρ' : IsSrc μ ρ') :
    ∀ q : ℕ, q + 1 ≤ c → ∀ (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), BilPos ψ μ (q + 1) σ B →
      ∀ (Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ),
      (∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG (q + 1) (tInt ψ ν μ (q + 1) σ B F Φ.1) (Rr Φ)) →
      ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
        IsQuotInt ν μX μG 1 (tIntOne ψ ν μ (q + 1) σ B F Φ.1) (toOne ν ρ' (q + 1) Rr Φ) := by
  haveI : ν.IsAddHaarMeasure := hν.1
  intro q
  induction q with
  | zero =>
    intro _ B _ Rr hRr Φ
    exact hRr Φ
  | succ q ih =>
    intro hqc B hB Rr hRr Φ
    have hq1 : 1 ≤ q + 1 := Nat.succ_le_succ (Nat.zero_le q)
    have hqlt : q + 1 < c := by omega

    obtain ⟨B₀, hB₀e, hB₀⟩ := ((GlobalTheory.RootEx.Exchange.exchange_isPos k n c (q + 1) hq1 hqlt ψ hψc hψ1 ν A σ hσ).2.2
      (SB (Matrix n n' k)) (omRight μ) B).2 ((bilPos_iff_isPos ψ μ _ σ B).1 hB)
    have hB₀' : BilPos ψ μ (q + 1) σ B₀ := (bilPos_iff_isPos ψ μ _ σ B₀).2 hB₀
    have hB₀f : ∀ Ψ, (⇑(B₀ Ψ) : A → ℂ) = exDown ν (q + 1) σ (⇑(B Ψ)) := fun Ψ => funext (hB₀e Ψ)

    have hsm' : IsSmoothRep ρ' := (_root_.GlobalTheory.PosOne.isSrc_exists_isSmoothRep k (n' ⊕ Fin (c + 1)) (n ⊕ Fin c) μ hμ).2 ρ' hρ'
    obtain ⟨Rr₀, hRr₀, hRr₀N⟩ := _root_.GlobalTheory.PosOne.RrLin.exists_linear_isQuotInt_tInt k n n' c (q + 1) hq1 hqlt.le ψ hψc hψ1 ν μ hμ μX μG A σ hσ B₀ hB₀' F ρ' hρ'
    have hIH := ih hqlt.le B₀ hB₀' Rr₀ hRr₀ Φ

    have hBup : ∀ Ψ v, B Ψ v = exUp ν (q + 1) σ (B₀ Ψ) v := by
      intro Ψ v
      rw [hB₀f Ψ]
      exact ((GlobalTheory.RootEx.exDown_exUp_and_exUp_exDown k n c (q + 1) hq1 hqlt ψ hψc hψ1 ν hν A σ hσ (B Ψ) v).2
        (hB.1 Ψ)).symm

    have hRrup : ∀ Φ', Rr Φ' = exUp ν (q + 1) ρ' Rr₀ Φ' := by
      intro Φ'
      have hst := _root_.GlobalTheory.PosOne.RrStep.rr_step k n n' c (q + 1) hq1 hqlt ψ hψc hψ1 ν hν μ hμ μX μG A σ hσ B₀ B hB₀' hBup F ρ' hρ' Rr₀ hRr₀ Φ'
      exact (GlobalTheory.QuotInt.quotInt_unique_exists k n c (q + 1 + 1) (by omega) hqc ν μX μG _).1 _ _ (hRr Φ') hst
    have hdown : exDown ν (q + 1) ρ' (⇑Rr) = ⇑Rr₀ := by
      funext v
      have hRrf : (⇑Rr : _ → ℂ) = exUp ν (q + 1) ρ' ⇑Rr₀ := funext hRrup
      rw [hRrf]
      exact (GlobalTheory.RootEx.exDown_exUp_and_exUp_exDown k n' (c + 1) (q + 1) hq1 (by omega) ψ hψc hψ1 ν hν _ ρ' hsm' Rr₀ v).1 hRr₀N
    have hval : toOne ν ρ' (q + 1 + 1) Rr Φ = toOne ν ρ' (q + 1) Rr₀ Φ := by
      rw [toOne_succ, hdown]
    have hfun : tIntOne ψ ν μ (q + 1 + 1) σ B F Φ.1 = tIntOne ψ ν μ (q + 1) σ B₀ F Φ.1 := by
      funext h
      simp only [tIntOne]
      rw [toOne_succ]
      congr 1
      funext v
      by_cases hm : opE ψ ν 1 (om μ 1 h Φ.1) ∈ SB (Matrix n n' k)
      · simp only [app, hm, dite_true]
        exact congrFun (hB₀f _).symm v
      · simp [app, hm, exDown]
    rw [hfun, hval]
    exact hIH

theorem GlobalTheory.PosOneIntegral.isQuotInt_toOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ P σ B) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ) (_ : ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG P (tInt ψ ν μ P σ B F Φ.1) (Rr Φ)) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), IsQuotInt ν μX μG 1 (tIntOne ψ ν μ P σ B F Φ.1) (toOne ν ρ' P Rr Φ) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c P hP1 hPc ψ hψc hψ1 ν hν μ hμ μX _ μG _ A _ _ σ hσ B hB F ρ' hρ' Rr hRr Φ
  obtain ⟨q, rfl⟩ : ∃ q, P = q + 1 := ⟨P - 1, by omega⟩
  exact GlobalTheory.PosOneIntegral.positionOne_invariantIntegral_exchange_step k n n' c ψ hψc hψ1 ν hν μ hμ μX μG A σ hσ F ρ' hρ' q hPc B hB Rr hRr Φ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixBlockColumnVanishingStepStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_block_column_vanishing_step : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → ∀ (j c : ℕ) (H : j + c = s) (q : Fin c), q.val + 1 ≤ S.ρ → q.val + 2 ≤ c → ∀ (x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k), (∀ r, x (Sum.inl r) (Sum.inr q.succ) = 0) → ∀ w : XIx (Fin κ) t (j + 1) → k, (S.T t).Phi j c H (x + Matrix.of fun r s' => if s' = Sum.inr q.succ then Sum.elim w 0 r else 0) = if ∀ r, valuation k (((S.ϖ ^ (q.val + 2) : kˣ) : k) * w r) < 1 then (S.T t).Phi j c H x else 0 := by
  first | exact @GlobalTheory.SymChain.ExchangeCol.phi_add_col | exact GlobalTheory.SymChain.ExchangeCol.phi_add_col | (intros; apply GlobalTheory.SymChain.ExchangeCol.phi_add_col <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionEqFlatMapFourierJacobiRow
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.RedFlatRow
open GlobalTheory.PartRed GlobalTheory.LocFlat

variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem mem_transSet_union_upSet (ρ : ℕ) (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :
    e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) ↔ Free (ρ + 1) e := by
  rcases e with ⟨r | l, s | i⟩ <;> simp only [transSet, upSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] <;> simp [Free] <;> omega

def freeEquiv (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) :
    {e // e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))} ≃
      {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} :=
  Equiv.subtypeEquivRight (mem_transSet_union_upSet ρ)

theorem fill_eq (ρ : ℕ) (lρ : Fin c) (hl : lρ.val = ρ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (y : {e // e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))} → k) :
    fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) (transSet ρ ∪ upSet ρ) x y =
      affPt (ρ + 1) (fun r s => x (Sum.inl r) (Sum.inl s)) (fun rs => y ((freeEquiv n n' c ρ).symm rs)) +
        rowAt n c (ρ + 1) (fun s => x (Sum.inr lρ) (Sum.inl s)) := by
  ext r q
  simp only [fillAt, affPt, Matrix.add_apply, Matrix.of_apply]
  by_cases hI : (r, q) ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))
  · have hF : Free (ρ + 1) (r, q) := (mem_transSet_union_upSet ρ _).1 hI
    rw [dite_eq_left hI, dite_eq_left hF]
    have h1 : (freeEquiv n n' c ρ).symm ⟨(r, q), hF⟩ = ⟨(r, q), hI⟩ := rfl
    rw [h1]
    rcases r with r | l <;> rcases q with s | i <;> simp [basePt, rowAt, Free, Matrix.fromBlocks] at hF ⊢ <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | (have hl' : l = lρ := Fin.ext (by omega); subst hl'; simp) | simp | omega | trace_state
  · have hF : ¬ Free (ρ + 1) (r, q) := fun hF => hI ((mem_transSet_union_upSet ρ _).2 hF)
    rw [dite_eq_right hI, dite_eq_right hF]
    by_cases hE : (r, q) ∈ (fixSet ρ ∪ lowSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))
    · rw [if_pos hE]
      simp only [fixSet, lowSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hE
      rcases r with r | l <;> rcases q with s | i <;> simp [basePt, rowAt, Free, Matrix.fromBlocks] at hF hE ⊢ <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | (have hl' : l = lρ := Fin.ext (by omega); subst hl'; simp) | simp | omega | trace_state
    · rw [if_neg hE]
      simp only [fixSet, lowSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hE
      rcases r with r | l <;> rcases q with s | i <;> simp [basePt, rowAt, Free, Matrix.fromBlocks] at hF hE ⊢ <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | (have hl' : l = lρ := Fin.ext (by omega); subst hl'; simp) | simp | omega | trace_state

theorem ch_add_rowAt (p : ℕ) (A : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (u : n' → k) :
    ch (A + rowAt n c p u) = ch A := by
  simp [ch, rowAt, Matrix.fromBlocks]

theorem piCongrLeft_freeEquiv [MeasurableSpace k] (ρ : ℕ)
    (y : {e // e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))} → k) :
    MeasurableEquiv.piCongrLeft (fun _ => k) (freeEquiv n n' c ρ) y =
      fun rs => y ((freeEquiv n n' c ρ).symm rs) := by
  funext rs
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]

end GlobalTheory.RedFlatRow


open GlobalTheory.RedFlatRow in
theorem GlobalTheory.RedFlatRow.red_eq_flRow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), c = 2 * ρ + 1 → ∀ (lρ : Fin c), lρ.val = ρ → ∀ (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.PartRed.red ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) (GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ) (GlobalTheory.PartRed.transSet ρ ∪ GlobalTheory.PartRed.upSet ρ) Φ x = GlobalTheory.LocFlat.flRow ψ ν (ρ + 1) Φ (Matrix.of fun r s => Sum.elim (fun r => x (Sum.inl r) (Sum.inl s)) (fun _ => x (Sum.inr lρ) (Sum.inl s)) r) := by
  intro k _ _ _ _ _ _ ψ ν hν n n' _ _ _ _ c ρ _ lρ hl Φ x
  classical
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite
  have hmp := MeasureTheory.measurePreserving_piCongrLeft (α := fun _ => k)
    (fun _ : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} => ν) (freeEquiv n n' c ρ)
  simp only [GlobalTheory.PartRed.red, GlobalTheory.LocFlat.flRow, opE]
  refine Eq.trans ?_ (hmp.integral_comp' _)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [piCongrLeft_freeEquiv, fill_eq ρ lρ hl x y, GlobalTheory.PartRed.chL_apply, ch_add_rowAt]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatCompAffineMatrix
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.AffineSB

theorem mem_SB_comp_affine : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R Q : Type) [Fintype R] [DecidableEq R] [Fintype Q] (A : GL R k) (a : Matrix R Q k) (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → (fun x => Φ (A.val * x + a)) ∈ SB (Matrix R Q k) := by
  intro k _ _ _ _ R Q _ _ _ A a Φ hΦ
  have hc : ∀ B : Matrix R R k, Continuous fun x : Matrix R Q k => B * x := fun B =>
    continuous_const.matrix_mul continuous_id
  let e : Matrix R Q k ≃ₜ Matrix R Q k :=
    { toFun := fun x => A.val * x + a
      invFun := fun y => (A⁻¹ : GL R k).val * (y - a)
      left_inv := fun x => by
        simp only [add_sub_cancel_right, ← Matrix.mul_assoc, Matrix.coe_units_inv]
        rw [Matrix.nonsing_inv_mul _ (by simpa using A.isUnit.map Matrix.detMonoidHom), Matrix.one_mul]
      right_inv := fun y => by
        simp only [← Matrix.mul_assoc, Matrix.coe_units_inv]
        rw [Matrix.mul_nonsing_inv _ (by simpa using A.isUnit.map Matrix.detMonoidHom), Matrix.one_mul, sub_add_cancel]
      continuous_toFun := (hc _).add continuous_const
      continuous_invFun := (hc _).comp (continuous_id.sub continuous_const) }
  exact ⟨hΦ.1.comp_continuous e.continuous, hΦ.2.comp_homeomorph e⟩

end GlobalTheory.AffineSB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPhiSupportPeriodicStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLevelChain_phi_support_periodic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (j c : ℕ) (H : j + c = s) (x z : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k), ((S.T t).Phi j c H x ≠ 0 → IntM ((embA (XIx (Fin κ) t (j + 1)) (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)))⁻¹.val * x * (embA (XIx (Fin κ) t j) (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1))).val)) ∧ (MaxM ((embA (XIx (Fin κ) t (j + 1)) (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)))⁻¹.val * z * (embA (XIx (Fin κ) t j) (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1))).val) → (S.T t).Phi j c H (x + z) = (S.T t).Phi j c H x) := by
  intro k _ _ _ _ s κ S t _ _ j c H x z
  set o := stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)
  set o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega)
  set F := typeFrame (k := k) S.ϖ o
  set F' := typeFrame (k := k) S.ϖ o'
  have hPhi : ∀ y, (S.T t).Phi j c H y = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      ((F.coords F' y).submatrix (ixSucc _ t j) id) := fun y => rfl
  constructor
  · intro hx i l
    rw [hPhi] at hx
    have := TypeDatum.intM_of_Phi_ne_zero _ _ hx ((ixSucc _ t j).symm (o.symm i)) (o'.symm l)
    simpa [LatFrame.coords, F, F', typeFrame] using this
  · intro hz
    rw [hPhi, hPhi]
    have e : F.coords F' (x + z) = F.coords F' x + F.coords F' z := by
      unfold LatFrame.coords; rw [Matrix.mul_add, Matrix.add_mul]; rfl
    rw [e]
    exact TypeDatum.Phi_add _ (S.tame _) _ (y := (F.coords F' z).submatrix (ixSucc _ t j) id) fun _ _ => hz _ _
end

