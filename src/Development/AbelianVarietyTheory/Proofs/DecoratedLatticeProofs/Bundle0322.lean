module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchrodingerIntertwinerIntegralMatrices
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0291
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExists
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocModU

theorem upAdd {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x x' : Matrix Y Y' k) :
    p.up FS FT (x + x') = p.up FS FT x + p.up FS FT x' := by
  unfold Place.up
  rw [Matrix.mul_add, Matrix.add_mul]
  ext i j
  simp [Matrix.map_apply]

theorem upZero {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) : p.up FS FT 0 = 0 := by
  unfold Place.up
  ext i j
  simp [Matrix.map_apply]

theorem charZero_of_place {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : Place D k) : CharZero k :=
  (RingHom.charZero_iff (ϕ := p.π.comp (incA D)) (RingHom.injective _)).1 inferInstance

theorem localModel_uniq_transport_exist : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∀ T₁ T₂, p.IsModel ψ FS FT T₁ → p.IsModel ψ FS FT T₂ → ∀ Φ₀, Φ₀ ≠ 0 → T₁ Φ₀ = T₂ Φ₀ → T₁ = T₂) ∧ (∀ T₁, p.IsModel ψ FS FT T₁ → ∀ A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (A f)) → (∀ f, IsThetaFunO ψ S T f → ∀ y : WO S T, IsHalf (p.e + cA D p.e) y → A (heisO ψ S T y f) = heisO ψ S T y (A f)) → p.IsModel ψ FS FT (A ∘ₗ T₁)) ∧ ∀ f₀, IsThetaFunO ψ S T f₀ → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) → heisO ψ S T (p.up FS FT x) f₀ = f₀) → (∀ y : WO S T, IsHalf (cA D p.e) y → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT x) y) = 1) → heisO ψ S T y f₀ = f₀) → ∃ T₁, p.IsModel ψ FS FT T₁ ∧ ∀ Φ : SB (Matrix Y Y' k), Φ.1 = Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) → T₁ Φ = f₀ := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ
  haveI : CharZero k := charZero_of_place p
  obtain ⟨⟨ψk, hψk⟩, hcn, -, -, -⟩ := _root_.GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨hcont, hne⟩ := hcn ψk hψk
  obtain ⟨hup, -, -, hsymk, hsurj⟩ := _root_.GlobalTheory.LocSympl.halves_at_split D k p Y Y' S T FS FT ψ ψk hψk
  obtain ⟨-, hec, -⟩ := p.split
  have hce : cA D p.e * p.e = 0 := by rw [mul_comm, hec]
  have hcce : cA D (cA D p.e) * cA D p.e = 0 := by rw [GlobalTheory.DualPairCheck.cA_cA, hec]
  have halfSum1 : ∀ u : WO S T, IsHalf p.e u → IsHalf (p.e + cA D p.e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hce, zero_mul, add_zero, hu i j]
  have halfSum2 : ∀ u : WO S T, IsHalf (cA D p.e) u → IsHalf (p.e + cA D p.e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hec, zero_mul, zero_add, hu i j]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro T₁ T₂ h₁ h₂ Φ₀ hΦ₀ h12
    let W : Submodule ℂ (Matrix Y Y' k → ℂ) := (LinearMap.ker (T₁ - T₂)).map (SB (Matrix Y Y' k)).subtype
    have memW : ∀ Φ : SB (Matrix Y Y' k), Φ.1 ∈ W ↔ T₁ Φ = T₂ Φ := by
      intro Φ
      constructor
      · rintro ⟨Ψ, hΨ, hΨe⟩
        have : Ψ = Φ := Subtype.ext hΨe
        subst this
        simpa [sub_eq_zero] using hΨ
      · intro h
        exact ⟨Φ, by simpa [sub_eq_zero] using h, rfl⟩
    have hWle : W ≤ SB (Matrix Y Y' k) := by
      rintro _ ⟨Ψ, -, rfl⟩
      exact Ψ.2
    have hWeq := _root_.GlobalTheory.IrredSB.sb_irreducible k Y Y' ψk hcont hne W hWle
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ x hx
        have hΦ' : T₁ Φ = T₂ Φ := (memW Φ).1 ⟨Φ, hΦ, rfl⟩
        refine (memW ⟨_, hx⟩).2 ?_
        rw [h₁.trans x Φ ⟨_, hx⟩ (fun t => rfl), h₂.trans x Φ ⟨_, hx⟩ (fun t => rfl), hΦ'])
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ b hb
        have hΦ' : T₁ Φ = T₂ Φ := (memW Φ).1 ⟨Φ, hΦ, rfl⟩
        obtain ⟨y, hy, hyb⟩ := hsurj b
        have hmod : ∀ t, (⟨_, hb⟩ : SB (Matrix Y Y' k)).1 t = ψ (symplO S T (p.up FS FT t) y) * Φ.1 t := by
          intro t
          show _ = _
          rw [hsymk t y hy, hyb t]
          rfl
        refine (memW ⟨_, hb⟩).2 ?_
        rw [h₁.modul y hy Φ _ hmod, h₂.modul y hy Φ _ hmod, hΦ'])
      Φ₀.1 ((memW Φ₀).2 h12) (fun h => hΦ₀ (Subtype.ext h))
    ext1 Φ
    have hm : Φ.1 ∈ W := by rw [hWeq]; exact Φ.2
    exact (memW Φ).1 hm
  ·
    intro T₁ h₁ A hA1 hA2
    refine ⟨fun Φ => hA1 _ (h₁.theta Φ), fun x Φ Φ' h => ?_, fun y hy Φ Φ' h => ?_⟩
    · show A (T₁ Φ') = heisO ψ S T (p.up FS FT x) (A (T₁ Φ))
      rw [h₁.trans x Φ Φ' h, hA2 _ (h₁.theta Φ) _ (halfSum1 _ (hup x).1)]
    · show A (T₁ Φ') = heisO ψ S T y (A (T₁ Φ))
      rw [h₁.modul y hy Φ Φ' h, hA2 _ (h₁.theta Φ) _ (halfSum2 _ hy)]
  ·
    intro f₀ hf₀ hfx hfy
    let Z := GlobalTheory.PlaceModel.half S T (cA D p.e)
    let χ : Matrix Y Y' k → Z → ℂ := fun t z => ψ (symplO S T (p.up FS FT t) z.1)
    have hZ : ∀ z : Z, IsHalf (cA D p.e) z.1 := fun z => (GlobalTheory.PlaceModel.isHalf_iff S T).2 z.2
    obtain ⟨Tm, htr, hmo, hvac, hspan⟩ := _root_.GlobalTheory.SchrodExist.exists_intertwiner_matrix k Y Y' Z χ
      (fun a b z => by simp only [χ, upAdd, GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul])
      (fun a z z' => by simp only [χ, AddSubgroup.coe_add, GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul])
      (fun z => by simp only [χ, upZero, GlobalTheory.PlaceModel.symplO_zero_left, AddChar.map_zero_eq_one])
      (fun a => by simp only [χ, ZeroMemClass.coe_zero, GlobalTheory.PlaceModel.symplO_zero_right, AddChar.map_zero_eq_one])
      (fun n hn z => by
        obtain ⟨z', hz', e⟩ := GlobalTheory.PlaceModel.half_div S T (cA D p.e) n hn z.1 z.2
        exact ⟨⟨z', hz'⟩, Subtype.ext (by rw [AddSubgroup.coe_nsmul]; exact e)⟩)
      (fun n hn z z' h => by
        apply Subtype.ext
        have h' : n • z.1 = n • z'.1 := by
          have := congrArg Subtype.val h
          simpa only [AddSubgroup.coe_nsmul] using this
        rw [← GlobalTheory.PlaceModel.inv_smul_nsmul S T hn z.1, h', GlobalTheory.PlaceModel.inv_smul_nsmul S T hn])
      (fun x hx => GlobalTheory.T.matrix_integral_of_addChar_trace_dual k Y Y' ψk hcont hne x fun b hb => by
        obtain ⟨y, hy, hyb⟩ := hsurj b
        have key : ∀ t, χ t ⟨y, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy⟩ = ((ψk (∑ r, ∑ q, b r q * t r q) : Circle) : ℂ) := by
          intro t
          show ψ _ = _
          rw [hsymk t y hy, hyb t]
        have := hx ⟨y, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy⟩ (fun u hu => by
          rw [key, hb u hu, Circle.coe_one])
        rw [key] at this
        exact Circle.ext (by simpa using this))
      (WO S T → ℂ) (fun x => GlobalTheory.PlaceModel.heisL S T ψ (p.up FS FT x)) (fun z => GlobalTheory.PlaceModel.heisL S T ψ z.1)
      (fun x x' f => by
        rw [GlobalTheory.PlaceModel.heisL_half S T ψ hce _ ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (hup x).1) _
          ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (hup x').1), upAdd])
      (fun z z' f => by
        rw [GlobalTheory.PlaceModel.heisL_half S T ψ hcce _ z.2 _ z'.2]
        rfl)
      (fun x z f => GlobalTheory.PlaceModel.heisL_comm S T ψ _ _ f)
      (fun f => by
        rw [upZero]
        funext w
        show ψ (symplOH S T w 0) * f (w + 0) = f w
        rw [symplOH, GlobalTheory.PlaceModel.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero])
      (fun f => by
        funext w
        show ψ (symplOH S T w 0) * f (w + 0) = f w
        rw [symplOH, GlobalTheory.PlaceModel.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero])
      f₀ (fun u hu => hfx u hu)
      (fun z hz => hfy z.1 (hZ z) hz)
    have hsplit := p.split
    have hstd : IsCharAF D.host.F ψ := hψ.1
    refine ⟨Tm, ⟨fun Φ => ?_, fun x Φ Φ' h => htr x Φ Φ' h, fun y hy Φ Φ' h =>
      hmo ⟨y, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy⟩ Φ Φ' h⟩, hvac⟩
    have hfin {a : WO S T} (ha : a.map (infPart D) = 0) {f : WO S T → ℂ}
        (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (heisO ψ S T a f) := by
      simpa using GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hstd f hf
        Unit Finset.univ (fun _ => a) (fun _ => 1) (fun _ _ => ha)
    have hzero : IsThetaFunO ψ S T 0 := by
      refine ⟨?_, ?_, continuous_const, ?_⟩
      · intro γ w; simp only [Pi.zero_apply, mul_zero]
      · exact ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
      · intro k L _ _ w; exact contDiff_const
    have hadd {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
        IsThetaFunO ψ S T (f + g) := by
      refine ⟨?_, ?_, hf.cont.add hg.cont, ?_⟩
      · intro γ w; simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
      · obtain ⟨U, hU, h1⟩ := hf.level
        obtain ⟨U', hU', h2⟩ := hg.level
        refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
        funext w
        have e1 := congrFun (h1 u hu.1 h0) w
        have e2 := congrFun (h2 u hu.2 h0) w
        unfold heisO at e1 e2 ⊢
        rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
      · intro k L h1 h2 w; exact (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)
    have hsmul (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
        IsThetaFunO ψ S T (c • f) := by
      refine ⟨?_, ?_, hf.cont.const_smul c, ?_⟩
      · intro γ w; rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
      · obtain ⟨U, hU, h1⟩ := hf.level
        refine ⟨U, hU, fun u hu h0 => ?_⟩
        funext w
        have e1 := congrFun (h1 u hu h0) w
        unfold heisO at e1 ⊢
        rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
      · intro k L h1 h2 w; exact contDiff_const.mul (hf.smooth k L h1 h2 w)
    have hs := hspan Φ
    generalize Tm Φ = g at hs
    induction hs using Submodule.span_induction with
    | mem _ hw =>
      obtain ⟨w, rfl⟩ := hw
      exact hfin (GlobalTheory.SplitScalar.half_fin hsplit (hup w.1).1)
        (hfin
          (GlobalTheory.SplitScalar.half_fin (GlobalTheory.SplitScalar.isSplitIdem_conj hsplit) (hZ w.2)) hf₀)
    | zero => exact hzero
    | add _ _ _ _ h1 h2 => exact hadd h1 h2
    | smul c _ _ h1 => exact hsmul c h1

end GlobalTheory.LocModU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSelfDualLatticeSplitPlaceDecomposition
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitSelfDual

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

def intMat : AddSubgroup (Matrix Y Y' k) where
  carrier := {x | ∀ r q, x r q ∈ 𝒪[k]}
  add_mem' hx hy r q := add_mem (hx r q) (hy r q)
  zero_mem' _ _ := zero_mem _
  neg_mem' hx r q := neg_mem (hx r q)

theorem isHalf_neg {S T : HSp D} {e : AE D} {y : WO S T} (h : IsHalf e y) : IsHalf e (-y) := fun i j => by
  rw [Matrix.neg_apply, mul_neg, h i j]

theorem symplO_neg_right (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  rw [← GlobalTheory.LatVac.symplHom_apply, map_neg]; rfl

theorem psi_neg_eq_one {ψ : AddChar (AF D.host.F) ℂ} {a : AF D.host.F} (h : ψ a = 1) : ψ (-a) = 1 := by
  have := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, one_mul] at this
  exact this.symm

theorem eq_zero_of_halves {e : AE D} (he : IsSplitIdem D e) {S T : HSp D} {y : WO S T} (h1 : IsHalf e y)
    (h2 : IsHalf (cA D e) y) : y = 0 := by
  ext i j
  rw [Matrix.zero_apply, ← h1 i j, ← h2 i j, ← mul_assoc, he.2.1, zero_mul]

def dualHalf (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (FS : Frame k S.rank Y')
    (FT : Frame k T.rank Y) : AddSubgroup (WO S T) where
  carrier := {y | IsHalf (cA D p.e) y ∧
    ∀ t : Matrix Y Y' k, (∀ r q, t r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT t) y) = 1}
  add_mem' {a b} ha hb := ⟨GlobalTheory.SplitScalar.isHalf_add ha.1 hb.1, fun t ht => by
    rw [GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul, ha.2 t ht, hb.2 t ht, one_mul]⟩
  zero_mem' := ⟨GlobalTheory.SplitScalar.isHalf_zero _, fun t _ => by
    rw [GlobalTheory.SplitScalar.symplO_zero_right, AddChar.map_zero_eq_one]⟩
  neg_mem' {a} ha := ⟨isHalf_neg ha.1, fun t ht => by
    rw [symplO_neg_right]; exact psi_neg_eq_one (ha.2 t ht)⟩

def lat (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (FS : Frame k S.rank Y')
    (FT : Frame k T.rank Y) : AddSubgroup (WO S T) :=
  (intMat (k := k) (Y := Y) (Y' := Y')).map (Witness.upH p FS FT) ⊔ dualHalf p ψ S T FS FT

section
variable (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)

theorem mem_lat {u : WO S T} : u ∈ lat p ψ S T FS FT ↔
    ∃ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ∧ ∃ y ∈ dualHalf p ψ S T FS FT, p.up FS FT x + y = u := by
  unfold lat
  rw [AddSubgroup.mem_sup]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, y, hy, h⟩
    exact ⟨x, hx, y, hy, h⟩
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨_, ⟨x, hx, rfl⟩, y, hy, h⟩

theorem up_mem_lat {x : Matrix Y Y' k} (hx : ∀ r q, x r q ∈ 𝒪[k]) : p.up FS FT x ∈ lat p ψ S T FS FT :=
  (mem_lat p ψ FS FT).2 ⟨x, hx, 0, zero_mem _, add_zero _⟩

theorem dualHalf_le_lat : dualHalf p ψ S T FS FT ≤ lat p ψ S T FS FT := le_sup_right

theorem half_e_of_mem {u : WO S T} (hu : u ∈ lat p ψ S T FS FT) (he : IsHalf p.e u) :
    ∃ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ∧ u = p.up FS FT x := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_lat p ψ FS FT).1 hu
  have hye : IsHalf p.e y := (Witness.half_add (Witness.up_half p FS FT x)).1 (by rwa [add_comm] at he)
  rw [eq_zero_of_halves p.split hye hy.1, add_zero]
  exact ⟨x, hx, rfl⟩

theorem half_c_of_mem {u : WO S T} (hu : u ∈ lat p ψ S T FS FT) (hc : IsHalf (cA D p.e) u) :
    u ∈ dualHalf p ψ S T FS FT := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_lat p ψ FS FT).1 hu
  have hxc : IsHalf (cA D p.e) (p.up FS FT x) := (Witness.half_add hy.1).1 hc
  rw [eq_zero_of_halves p.split (Witness.up_half p FS FT x) hxc, zero_add]
  exact hy

end

theorem selfDual_lattice_split : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), ∃ Λ : AddSubgroup (WO S T), (∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1) ∧ (∀ y, IsHalf p.e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D p.e) l ∧ ψ (symplO S T l y) ≠ 1) ∧ (∀ y, IsHalf (cA D p.e) y → y ∉ Λ → ∃ l ∈ Λ, IsHalf p.e l ∧ ψ (symplO S T l y) ≠ 1) ∧ (∀ x : Matrix Y Y' k, p.up FS FT x ∈ Λ ↔ ∀ r q, x r q ∈ 𝒪[k]) ∧ (∀ u ∈ Λ, IsHalf p.e u → ∃ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ∧ u = p.up FS FT x) ∧ (∀ u ∈ Λ, IsHalf (cA D p.e) u → ∀ t : Matrix Y Y' k, (∀ r q, t r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT t) u) = 1) := by
  intro D k _ _ _ _ p ψ hψ S T Y Y' _ _ _ _ FS FT
  obtain ⟨⟨ψk, hψk⟩, hcont, -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨hψc, hψ1⟩ := hcont ψk hψk
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψk hψc hψ1
  obtain ⟨-, -, hiso, hpsi, hpair⟩ := GlobalTheory.LocSympl.halves_at_split D k p Y Y' S T FS FT ψ ψk hψk
  have hconj : IsSplitIdem D (cA D p.e) := GlobalTheory.SplitScalar.isSplitIdem_conj p.split
  refine ⟨lat p ψ S T FS FT, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro u hu u' hu'
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_lat p ψ FS FT).1 hu
    obtain ⟨x', hx', y', hy', rfl⟩ := (mem_lat p ψ FS FT).1 hu'
    have h4 : symplO S T y y' = 0 := GlobalTheory.SplitScalar.half_orth hconj hy.1 hy'.1
    have h3 : ψ (symplO S T y (p.up FS FT x')) = 1 := by
      rw [GlobalTheory.SplitScalar.symplO_skew]; exact psi_neg_eq_one (hy.2 x' hx')
    rw [GlobalTheory.LatVac.symplO_add_left, GlobalTheory.LatVac.symplO_add_right, GlobalTheory.LatVac.symplO_add_right, hiso, h4,
      zero_add, add_zero, AddChar.map_add_eq_mul, hy'.2 x hx, h3, one_mul]
  ·
    intro y hy hyΛ
    have hyx : p.up FS FT (p.down FS FT y) = y := Witness.up_down p FS FT hy
    have hx : ¬ ∀ r q, p.down FS FT y r q ∈ 𝒪[k] := fun hx => hyΛ (hyx ▸ up_mem_lat p ψ FS FT hx)
    push_neg at hx
    obtain ⟨r, q, hrq⟩ := hx
    set a := p.down FS FT y r q with ha
    have hrq' : ¬ valuation k a ≤ 1 := fun h => hrq ((Valuation.mem_integer_iff _ _).2 h)
    have ha0 : a ≠ 0 := by rintro h; rw [h, map_zero] at hrq'; exact hrq' zero_le'
    have hc0 : 0 < valuation k (c : k) := by simp [zero_lt_iff]
    have hcv : ¬ valuation k (c * a) ≤ valuation k (c : k) := by
      rw [map_mul]; intro h
      have h' : valuation k (c : k) * valuation k a ≤ valuation k (c : k) * 1 := by rwa [mul_one]
      exact hrq' ((mul_le_mul_iff_of_pos_left hc0).1 h')
    obtain ⟨z, hz, hzne⟩ : ∃ z, valuation k z ≤ valuation k (c * a) ∧ ψk z ≠ 1 := by
      by_contra hcon; push_neg at hcon; exact hcv ((hc _).1 hcon)
    have hsum : ∀ t : Matrix Y Y' k, ∑ r', ∑ q', Matrix.single r q (z / a) r' q' * t r' q' = z / a * t r q := by
      intro t; simp [Matrix.single_apply, ite_and]
    obtain ⟨y', hy'c, hy'p⟩ := hpair (Matrix.single r q (z / a))
    have hy'Λ : y' ∈ dualHalf p ψ S T FS FT := by
      refine ⟨hy'c, fun t ht => ?_⟩
      rw [hpsi t y' hy'c, hy'p, hsum]
      have ha0' : 0 < valuation k a := by simp [zero_lt_iff, ha0]
      have hv : valuation k (z / a * t r q) ≤ valuation k (c : k) := by
        rw [map_mul, map_div₀]
        calc valuation k z / valuation k a * valuation k (t r q) ≤ valuation k z / valuation k a * 1 := by
              gcongr; exact (Valuation.mem_integer_iff _ _).1 (ht r q)
          _ ≤ valuation k (c : k) := by rw [mul_one, div_le_iff₀ ha0', ← map_mul]; exact hz
      rw [(hc c).2 le_rfl _ hv, Circle.coe_one]
    refine ⟨y', dualHalf_le_lat p ψ FS FT hy'Λ, hy'c, GlobalTheory.SplitScalar.psi_skew_ne ?_⟩
    rw [← hyx, hpsi _ y' hy'c, hy'p, hsum, ← ha, div_mul_cancel₀ z ha0]
    exact fun h => hzne (Circle.ext (by rw [h, Circle.coe_one]))
  ·
    intro y hy hyΛ
    have hyd : y ∉ dualHalf p ψ S T FS FT := fun h => hyΛ (dualHalf_le_lat p ψ FS FT h)
    have : ¬ ∀ t : Matrix Y Y' k, (∀ r q, t r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT t) y) = 1 :=
      fun h => hyd ⟨hy, h⟩
    push_neg at this
    obtain ⟨t, ht, hne⟩ := this
    exact ⟨p.up FS FT t, up_mem_lat p ψ FS FT ht, Witness.up_half p FS FT t, hne⟩
  ·
    intro x
    refine ⟨fun hx => ?_, fun hx => up_mem_lat p ψ FS FT hx⟩
    obtain ⟨x', hx', hxx⟩ := half_e_of_mem p ψ FS FT hx (Witness.up_half p FS FT x)
    have := congrArg (p.down FS FT) hxx
    rw [Witness.down_up, Witness.down_up] at this
    exact this ▸ hx'
  · intro u hu he
    exact half_e_of_mem p ψ FS FT hu he
  · intro u hu hc' t ht
    exact (half_c_of_mem p ψ FS FT hu hc').2 t ht

end GlobalTheory.SplitSelfDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemPerOInfHalfAO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HalfAConj
open GlobalTheory.LatVac

theorem conjPl_eq_conjP {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.L2.DIV.conjPl P = Formalism.L2.Col.conjPrime₂ P := by
  apply HeightOneSpectrum.ext
  apply Ideal.ext
  intro r
  show Formalism.L2.DIV.starOHom r ∈ P.asIdeal ↔ Formalism.L2.Col.cO E r ∈ P.asIdeal
  have : Formalism.L2.DIV.starOHom r = Formalism.L2.Col.cO E r := by
    first
      | rfl
      | (apply RingOfIntegers.ext; simp [Formalism.L2.DIV.starOHom, Formalism.L2.DIV.starO_coe, Formalism.L2.Col.cO])
  rw [this]

set_option maxHeartbeats 1000000 in
theorem mem_perO_inf_halfAO : ∀ (D : D7) (S T : HSp D), D.host.ccK = ⊤ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ c : ℕ, 0 < c → ∀ M ∈ GlobalTheory.LatVac.latRat S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)), (∃ w ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True), cA D e • GlobalTheory.LatVac.finTens 1 M = c • w) → Matrix.toLin' M ∈ (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ⊓ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c := by
  intro D S T hcc e SS hE N N' hN hN' c hc M hM hw
  obtain ⟨w, hw, hcw⟩ := hw
  have h1 : Matrix.toLin' M ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' := by
    have := (GlobalTheory.AdForm.RatLat.mem_latRat_iff_perO N' hN M).1 hM
    rwa [GlobalTheory.AdForm.RatLat.AA_eq hcc] at this
  refine Submodule.mem_inf.2 ⟨h1, ?_⟩
  have hcE : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have h0 : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hE)
  have hconj : ((LinearMap.toMatrix' ((c : D.host.E)⁻¹ • Matrix.toLin' M)).map fun r => cA D e * incA D r : WO S T) = w := by
    ext i j
    have hij := congrFun (congrFun hcw i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hij
    have e1 : cA D e * finTens 1 M i j = cA D e * incA D (M i j) := by
      refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
      · rw [RingHom.map_mul, RingHom.map_mul, h0, zero_mul, zero_mul]
      · rw [RingHom.map_mul, RingHom.map_mul]
        rfl
    have e2 : LinearMap.toMatrix' ((c : D.host.E)⁻¹ • Matrix.toLin' M) i j = (c : D.host.E)⁻¹ * M i j := by
      have e2' : (c : D.host.E)⁻¹ • Matrix.toLin' M = Matrix.toLin' ((c : D.host.E)⁻¹ • M) :=
        (map_smul Matrix.toLin' _ _).symm
      rw [e2', LinearMap.toMatrix'_toLin']
      rfl
    rw [Matrix.map_apply, e2, RingHom.map_mul, mul_left_comm, ← e1, hij, nsmul_eq_mul, ← mul_assoc]
    have e3 : incA D (c : D.host.E)⁻¹ * (c : AE D) = 1 := by
      rw [← map_natCast (incA D) c, ← RingHom.map_mul, inv_mul_cancel₀ hcE, map_one]
    rw [e3, one_mul]
  have hloc := (_root_.GlobalTheory.AdForm.HalfLat.half_mem_latO_iff D S T hcc (cA D e) _ (Formalism.IndefR.Fin.LevelGroupLemmas.isIdemSum_conj hE) N N' hN hN' _).1
    (hconj ▸ hw)
  rw [halfAO, Formalism.L2.Ker.mem_twO]
  intro Q
  by_cases hQ : Q ∈ SS
  · have ex : expS SS Q = 1 := by simp [expS, hQ]
    rw [ex]
    have e4 : (((c : D.host.E) ^ (-(1 : ℤ)))⁻¹) = (c : D.host.E) := by simp
    rw [e4]
    exact Formalism.L2.Ker.le_locP' _ _ (Formalism.L2.Ker.nat_smul_mem _ c h1)
  · by_cases hQ' : Formalism.L2.Col.conjPrime₂ Q ∈ SS
    · have ex : expS SS Q = -1 := by simp [expS, hQ, hQ']
      rw [ex]
      have e4 : (((c : D.host.E) ^ (-(-1 : ℤ)))⁻¹) = (c : D.host.E)⁻¹ := by simp
      rw [e4]
      refine hloc Q (Finset.mem_image.2 ⟨Formalism.L2.Col.conjPrime₂ Q, hQ', ?_⟩)
      rw [conjPl_eq_conjP, Formalism.L2.Ker.conjP_conjP']
    · have ex : expS SS Q = 0 := by simp [expS, hQ, hQ']
      rw [ex]
      simpa using Formalism.L2.Ker.le_locP' _ _ h1

end GlobalTheory.HalfAConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NeZeroOfIsIdemAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.LevelPlaces

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

variable {D : D7}

theorem splitAt_of {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} {ε : AF D.host.F} (he : IsSplitIdem D e)
    (hε : IsPlaceIdem D v ε) (h : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) : SplitAt D v e := by
  obtain ⟨α, rfl, h3, h4⟩ := hε
  have : α = singleV D.host.F v 1 := af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [h3, evalV_singleV_same]
    · rw [h4 w hw, evalV_singleV_ne _ v _ hw]
  subst this
  exact ⟨he.1, he.2.1, h⟩

theorem ne_zero_of_isIdemAt {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : Formalism.L2.NTheta.IsIdemAt e P) : e ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  exact ((hP.2 x hx0).1 hx) (by rw [zero_mul, map_zero]; exact zero_mem _)

end GlobalTheory.LevelPlaces
end
end

