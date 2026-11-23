module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0312
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0321
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0138
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimeIdempotentIntegralAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0090

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRationalPointsStabiliserFrame
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.transport_rational_points : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (Φ : Hfin X u ≃* Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), (∀ (h : Hfin X u) y, RepF X wt ιA (h : X.B.I.Gf) y ↔ Φ h = y) → (∀ γ : Gam X u, ∃ g : GL (Fin (D.R.N 0)) D.host.E, g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) ∧ (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g) ∧ (∀ g : GL (Fin (D.R.N 0)) D.host.E, g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → ∃ γ : Gam X u, (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g) ∧ ∀ (γ : Gam X u) (g : GL (Fin (D.R.N 0)) D.host.E), (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g → sTil X wt (iotaI X u γ : X.B.I.Ginf) = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) g.1 := by
  intro D X u wt ιA hW hA Φ hΦ
  have hmem : ∀ g : GL (Fin (D.R.N 0)) D.host.E, g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g ∈ Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    intro g hg
    refine Formalism.UG.P.bc_mem _ _ _ ?_ _ g hg
    ext x
    simp [Formalism.UG.sigR, Formalism.UG.inclE]
  have key : ∀ (h : Hfin X u) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E) (g : GL (Fin (D.R.N 0)) D.host.E), X.B.I.fmat (h : X.B.I.Gf) = γ₀.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) → (∀ j, γ₀ *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i)) → (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = y₀.map X.ιE → ∀ hg : g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)), (Φ h).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g := by
    intro h γ₀ y₀ g hf hq hgy hg
    have hr := GlobalTheory.T.rational_matrix_represents_adelic_point_in_frame D X wt ιA hA h γ₀ y₀ hf hq ⟨_, hmem g hg⟩ (by
      show (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map _ = _
      rw [hgy])
    rw [(hΦ h _).1 hr]
  have hinj : ∀ g g' : GL (Fin (D.R.N 0)) D.host.E, Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g' → g = g' := by
    intro g g' h
    haveI : Nontrivial (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      let v : HeightOneSpectrum (𝓞 D.host.F) :=
        ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField D.host.F)⟩
      exact ⟨⟨0, 1, fun h => by
        have := congrArg (fun x : FiniteAdeleRing (𝓞 D.host.F) D.host.F => x v) h
        exact zero_ne_one (α := v.adicCompletion D.host.F) this⟩⟩
    have hc := congrArg Units.val h
    rw [Formalism.UG.P.bc_coe, Formalism.UG.P.bc_coe] at hc
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact Formalism.UG.P.inclE_injective D.host.F D.host.E _ (congrFun (congrFun hc i) j)
  refine ⟨fun γ => ?_, fun g hg => ?_, fun γ g hγg => ?_⟩
  · obtain ⟨γ₀, hu, -, hf, hfix⟩ := GlobalTheory.T.rationalStabiliser_point_from_unitary_fixing_frame D X u γ
    obtain ⟨y₀, hy, hq⟩ := _root_.GlobalTheory.St.unitary_fix_acts_on_complement_frame D X u wt hW γ₀ hu hfix
    obtain ⟨g, hgy⟩ := _root_.GlobalTheory.St.gramN_unitary_isUnit D X u wt hW y₀ hy
    have hg : g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) :=
      (_root_.GlobalTheory.St.mem_UJ_gramN_iff_map_symm D X g).2 (by
        have e : (y₀.map X.ιE).map X.ιE.symm = y₀ := Matrix.ext fun i j => by simp
        rw [hgy, e]; exact hy)
    exact ⟨g, hg, key (iotaF X u γ) γ₀ y₀ g hf hq hgy hg⟩
  · obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, y₀ = (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map X.ιE.symm := ⟨_, rfl⟩
    have hy := (_root_.GlobalTheory.St.mem_UJ_gramN_iff_map_symm D X g).1 hg
    rw [← hy₀] at hy
    obtain ⟨γ₀, hu, hfix, hq⟩ := _root_.GlobalTheory.St.rational_unitary_extend_by_identity D X u wt hW y₀ hy
    obtain ⟨γ, -, hf⟩ := GlobalTheory.T.rational_unitary_fixing_mem_rationalStabiliser D X u γ₀ hu hfix
    have hgy : (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = y₀.map X.ιE :=
      Matrix.ext fun i j => by simp [hy₀]
    exact ⟨γ, key (iotaF X u γ) γ₀ y₀ g hf hq hgy hg⟩
  · obtain ⟨γ₀, hu, hinf, hf, hfix⟩ := GlobalTheory.T.rationalStabiliser_point_from_unitary_fixing_frame D X u γ
    obtain ⟨y₀, hy, hq⟩ := _root_.GlobalTheory.St.unitary_fix_acts_on_complement_frame D X u wt hW γ₀ hu hfix
    obtain ⟨g', hgy⟩ := _root_.GlobalTheory.St.gramN_unitary_isUnit D X u wt hW y₀ hy
    have hg' : g' ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) :=
      (_root_.GlobalTheory.St.mem_UJ_gramN_iff_map_symm D X g').2 (by
        have e : (y₀.map X.ιE).map X.ιE.symm = y₀ := Matrix.ext fun i j => by simp
        rw [hgy, e]; exact hy)
    have e1 := key (iotaF X u γ) γ₀ y₀ g' hf hq hgy hg'
    have e2 : g = g' := hinj g g' (hγg.symm.trans e1)
    subst e2
    rw [hgy]
    exact _root_.GlobalTheory.St.sTil_eq_atInf_of_rational D X u wt hW _ γ₀ y₀ hinf hq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsDualModLevel
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.DualMod

open Formalism.L2.SG.Pf.unitaryCongruence

section Gen

variable (I : AutInst)

theorem hform_mulVec_conj {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J M : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  have hd : ∀ (J : Matrix n n A) (x y : n → A), Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
    intro J x y
    simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
  have hσ : σ ∘ (M *ᵥ x) = M.map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ M x i
  rw [hd, hd, hσ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, Formalism.UG.cT, Matrix.mul_assoc]

theorem hA_unitary (x : I.Gf) (u v : VA I) : hA I (I.fmat x *ᵥ u) (I.fmat x *ᵥ v) = hA I u v := by
  have h : Formalism.UG.cT (sigA I) (I.fmat x) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * I.fmat x =
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2
  unfold hA
  rw [hform_mulVec_conj, h]

theorem zmod_add {g : ℕ} {a b : I.E ⊗[I.F] Af I.F} (ha : ZMod' I g a) (hb : ZMod' I g b) :
    ZMod' I g (a + b) := by
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact ⟨s + t, add_mem hs ht, by ring⟩

theorem zmod_mul {g : ℕ} {a c : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E) (ha : ZMod' I g a) :
    ZMod' I g (c * a) := by
  obtain ⟨s, hs, rfl⟩ := ha
  exact ⟨c * s, mul_mem hc hs, by ring⟩

theorem zmod_zero (g : ℕ) : ZMod' I g 0 := ⟨0, zero_mem _, by simp⟩

theorem hA_zero_left (y : VA I) : hA I 0 y = 0 := by simp [hA, Formalism.UG.hform]
theorem hA_zero_right (y : VA I) : hA I y 0 = 0 := by simp [hA, Formalism.UG.hform]

theorem hA_mL_left {g : ℕ} {m y : VA I} (hm : m ∈ mL I g) (hy : y ∈ I.Lf) : ZMod' I g (hA I m y) := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨x, hx, rfl⟩ := hm
    rw [hA_smul_left, map_natCast]
    exact ⟨hA I x y, hA_int I hx hy, rfl⟩
  | zero => rw [hA_zero_left]; exact zmod_zero I g
  | add a b _ _ ha hb => rw [hA_add_left]; exact zmod_add I ha hb
  | smul c a _ ha =>
    show ZMod' I g (hA I ((c : I.E ⊗[I.F] Af I.F) • a) y)
    rw [hA_smul_left]; exact zmod_mul I (sigA_mem I c.2) ha

theorem hA_mL_right {g : ℕ} {m y : VA I} (hm : m ∈ mL I g) (hy : y ∈ I.Lf) : ZMod' I g (hA I y m) := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨x, hx, rfl⟩ := hm
    rw [hA_smul_right]
    exact ⟨hA I y x, hA_int I hy hx, rfl⟩
  | zero => rw [hA_zero_right]; exact zmod_zero I g
  | add a b _ _ ha hb => rw [hA_add_right]; exact zmod_add I ha hb
  | smul c a _ ha =>
    show ZMod' I g (hA I y ((c : I.E ⊗[I.F] Af I.F) • a))
    rw [hA_smul_right]; exact zmod_mul I c.2 ha

theorem mL_le (g : ℕ) : mL I g ≤ I.Lf := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [Nat.cast_smul_eq_nsmul]
  exact I.Lf.nsmul_mem hx g

end Gen

theorem dual_mod : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → (∀ i, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i) - X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ mL X.B.I X.B.g ∧ (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g) → ∀ i j, ∃ t ∈ OAd D.host.F D.host.E, hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) (bd i) (b j) - (if i = j then ιA X.ew else 0) = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) * t := by
  intro D X u wt ιA hW hι c p b bd hb hbd hm i j
  obtain ⟨-, h2, -⟩ := _root_.GlobalTheory.St.G.MHat.mhat_coords D X u wt ιA hW hι
  have hY : ∀ i, X.B.I.fmat (X.xu u) *ᵥ X.bw i ∈ X.B.I.Lf :=
    fun i => K_mv X.B.I (X.xu_K u) (X.vectorsInLattice.2.2 i).1
  have hYd : ∀ i, X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ X.B.I.Lf :=
    fun i => K_mv X.B.I (X.xu_K u) (X.vectorsInLattice.2.2 i).2
  have hm1 : embA X wt ιA (b j) - X.B.I.fmat (X.xu u) *ᵥ X.bw j ∈ mL X.B.I X.B.g := by
    rw [hb j]; exact (hm j).1
  have hm2 : embA X wt ιA (bd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i ∈ mL X.B.I X.B.g := by
    rw [hbd i]; exact (hm i).2
  have key : ZMod' X.B.I X.B.g
      (hA X.B.I (embA X wt ιA (bd i)) (embA X wt ιA (b j)) - if i = j then X.ew else 0) := by
    generalize hm' : embA X wt ιA (b j) - X.B.I.fmat (X.xu u) *ᵥ X.bw j = m' at hm1
    generalize hmm : embA X wt ιA (bd i) - X.B.I.fmat (X.xu u) *ᵥ X.bwd i = m at hm2
    have e1 : embA X wt ιA (b j) = X.B.I.fmat (X.xu u) *ᵥ X.bw j + m' := by rw [← hm']; abel
    have e2 : embA X wt ιA (bd i) = X.B.I.fmat (X.xu u) *ᵥ X.bwd i + m := by rw [← hmm]; abel
    rw [e1, e2, hA_add_left, hA_add_right, hA_add_right, hA_unitary]
    have e3 : hA X.B.I (X.bwd i) (X.bw j) + hA X.B.I (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) m' +
        (hA X.B.I m (X.B.I.fmat (X.xu u) *ᵥ X.bw j) + hA X.B.I m m') - (if i = j then X.ew else 0) =
        (hA X.B.I (X.bwd i) (X.bw j) - (if i = j then X.ew else 0)) +
          hA X.B.I (X.B.I.fmat (X.xu u) *ᵥ X.bwd i) m' +
          (hA X.B.I m (X.B.I.fmat (X.xu u) *ᵥ X.bw j) + hA X.B.I m m') := by ring
    rw [e3]
    refine zmod_add _ (zmod_add _ (X.bw_dual i j) (hA_mL_right _ hm1 (hYd i)))
      (zmod_add _ (hA_mL_left _ hm2 (hY j)) (hA_mL_left _ hm2 (mL_le _ _ hm1)))
  obtain ⟨t, ht, he⟩ := key
  refine ⟨ιA t, (hι.2 t).1 ht, ?_⟩
  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) =
      ιA (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    rw [map_natCast, X.g_eq]
  have hif : (if i = j then ιA X.ew else 0) = ιA (if i = j then X.ew else 0) := by
    split_ifs <;> simp
  rw [← h2, hg, hif, ← map_sub, he, map_mul]

end GlobalTheory.St.G.DualMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedTypeVectorsFixedByChosenPlacesIdempot
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.FrameEps

theorem beps : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), ∀ (b bd : Fin D.R.k → Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F), (∀ i, embA X wt ιA (b i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) → (∀ i, embA X wt ιA (bd i) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)) → (∀ i, b i = ιA X.ew • b i) ∧ ∀ i, bd i = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew) • bd i := by
  intro D X u wt ιA hW hA c p b bd hb hbd
  have hinj := (_root_.GlobalTheory.St.G.MHat.mhat_coords D X u wt ιA hW hA).2.2.1
  have semi : ∀ a x, embA X wt ιA (ιA a • x) = a • embA X wt ιA x := by
    intro a x
    simp only [embA, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, map_mul,
      RingEquiv.symm_apply_apply, mul_smul]
  constructor
  · intro i
    apply hinj
    rw [semi, hb, smul_comm X.ew, ← map_smul p X.ew, ← Matrix.mulVec_smul _ X.ew, ← X.bw_w i]
  · intro i
    apply hinj
    have hs : Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (Ad D.host.F) (ιA X.ew) = ιA (sigA X.B.I X.ew) :=
      (GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hA X.ew).symm
    rw [hs, semi, hbd, smul_comm (sigA X.B.I X.ew), ← map_smul p (sigA X.B.I X.ew),
      ← Matrix.mulVec_smul _ (sigA X.B.I X.ew), ← X.bwd_w i]

end GlobalTheory.St.G.FrameEps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoSidedSizeFunctionPosInvariantContinuous
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.TwoSided

open GlobalTheory.Mom.LowVec

theorem exists_coord {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (a : Fin (r + 1)) :
    ∃ i : Fin (2 * r + k + 1), a.val ≤ i.val ∧ fvec k r z a i ≠ 0 := by
  by_cases ha : a.val < r
  · refine ⟨eI k r ⟨a.val, ha⟩, le_of_eq rfl, ?_⟩
    simp only [fvec, dif_pos ha, bvec, Pi.single_eq_same]
    exact one_ne_zero
  ·
    have hz0 : ∃ i, z i ≠ 0 := by
      by_contra h
      push_neg at h
      have : z = 0 := funext h
      subst this
      simp [Tz, herm] at hT
    obtain ⟨i, hi⟩ := hz0
    have hri : r ≤ i.val := by
      by_contra h
      exact hi (hz i (Or.inl (Nat.lt_of_not_le h)))
    refine ⟨i, le_trans (Nat.le_of_lt_succ a.isLt) hri, ?_⟩
    simp only [fvec, dif_neg ha]
    exact hi

theorem lA_pos {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {x : Mat k r} (hx : x ∈ GG k r) (a : Fin (r + 1)) : 0 < lA k r z x a := by
  obtain ⟨i, hai, hi⟩ := exists_coord hz hT a
  have hu : IsUnit x.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hx
  have hc : 0 < ∑ j, ‖x i j‖ + 1 := by positivity

  have key : ∀ y ∈ Submodule.span ℂ (Set.range fun b : {b : Fin r // b.val < a.val} =>
      Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r b.1)),
      ‖fvec k r z a i‖ / (∑ j, ‖x i j‖ + 1) ≤ eucl (x⁻¹ *ᵥ (fvec k r z a - y)) := by
    intro y hy
    have hy' : y ∈ GlobalTheory.Mom.LowVec.flagSpan k r a := hy
    have hyi : y i = 0 := (GlobalTheory.Mom.LowVec.mem_flagSpan.1 hy') i hai
    set w := x⁻¹ *ᵥ (fvec k r z a - y) with hw
    have hv : fvec k r z a - y = x *ᵥ w := by
      rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv x hu, Matrix.one_mulVec]
    have hvi : fvec k r z a i = ∑ j, x i j * w j := by
      have := congrFun hv i
      simp only [Pi.sub_apply, hyi, sub_zero] at this
      rw [this]
      rfl
    have hwe : 0 ≤ eucl w := Real.sqrt_nonneg _
    have hle : ‖fvec k r z a i‖ ≤ (∑ j, ‖x i j‖ + 1) * eucl w := by
      rw [hvi]
      calc ‖∑ j, x i j * w j‖ ≤ ∑ j, ‖x i j * w j‖ := norm_sum_le _ _
        _ = ∑ j, ‖x i j‖ * ‖w j‖ := by simp only [norm_mul]
        _ ≤ ∑ j, ‖x i j‖ * eucl w := by
          gcongr with j
          exact GlobalTheory.Amp.LInv.norm_le_eucl w j
        _ = (∑ j, ‖x i j‖) * eucl w := by rw [Finset.sum_mul]
        _ ≤ (∑ j, ‖x i j‖ + 1) * eucl w := by nlinarith
    rw [div_le_iff₀ hc]
    linarith
  unfold lA
  refine lt_of_lt_of_le (div_pos (norm_pos_iff.mpr hi) hc) ?_
  refine le_csInf ⟨_, 0, Submodule.zero_mem _, rfl⟩ ?_
  rintro t ⟨y, hy, rfl⟩
  exact key y hy

theorem Sg2_invariant_continuousOn_one_le_bounds : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → (∀ x ∈ GG k r, ∀ a, 0 < lA k r z x a) ∧ (∀ x ∈ GG k r, ∀ s ∈ Sset k r z, ∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), Sg2 k r z (s * x * κ) = Sg2 k r z x) ∧ ContinuousOn (Sg2 k r z) (GG k r) ∧ ∀ x, 1 ≤ Sg2 k r z x ∧ Sg k r z x ≤ Sg2 k r z x ∧ (∀ a, lA k r z x a ≤ Sg2 k r z x ∧ (lA k r z x a)⁻¹ ≤ Sg2 k r z x) ∧ (Sg2 k r z x = 1 ∨ ∃ a, Sg2 k r z x = max (lA k r z x a) (lA k r z x a)⁻¹) := by
  intro k r z hz hT
  have hpos : ∀ x ∈ GG k r, ∀ a, 0 < lA k r z x a := fun x hx a => lA_pos hz hT hx a
  obtain ⟨hinv, -, hSg⟩ := GlobalTheory.Amp.LInv.lengths_basic k r z hz
  refine ⟨hpos, ?_, ?_, ?_⟩
  · intro x hx s hs κ hκ
    have h := (hinv x hx s hs κ hκ).1
    simp only [Sg2, h]
  · have hc := (GlobalTheory.Amp.LenCont.lA_Sg_continuousOn k r z).1
    exact GlobalTheory.Amp.LenCont.fold_continuousOn (GG k r) (fun a x => max (lA k r z x a) (lA k r z x a)⁻¹)
      (fun a => continuous_max.comp_continuousOn (ContinuousOn.prodMk (hc a) (ContinuousOn.inv₀ (hc a) fun x hx => (hpos x hx a).ne'))) Finset.univ
  · intro x
    have hle : ∀ a, max (lA k r z x a) (lA k r z x a)⁻¹ ≤ Sg2 k r z x := fun a =>
      (Finset.le_fold_max _).2 (Or.inr ⟨a, Finset.mem_univ _, le_rfl⟩)
    have h1 : 1 ≤ Sg2 k r z x := (Finset.le_fold_max _).2 (Or.inl le_rfl)
    refine ⟨h1, ?_, fun a => ⟨(le_max_left _ _).trans (hle a), (le_max_right _ _).trans (hle a)⟩, ?_⟩
    · exact (Finset.fold_max_le _).2 ⟨h1, fun a _ => (le_max_left _ _).trans (hle a)⟩
    ·
      have key : ∀ s : Finset (Fin (r + 1)), s.fold max 1 (fun a => max (lA k r z x a) (lA k r z x a)⁻¹) = 1 ∨
          ∃ a, s.fold max 1 (fun a => max (lA k r z x a) (lA k r z x a)⁻¹) = max (lA k r z x a) (lA k r z x a)⁻¹ := by
        intro s
        refine Finset.induction_on s ?_ ?_
        · left
          simp
        · intro a s ha ih
          rw [Finset.fold_insert ha]
          rcases max_choice (max (lA k r z x a) (lA k r z x a)⁻¹)
              (s.fold max 1 (fun a => max (lA k r z x a) (lA k r z x a)⁻¹)) with h | h
          · exact Or.inr ⟨a, h⟩
          · rw [h]
            exact ih
      exact key Finset.univ

end GlobalTheory.Amp.TwoSided
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeRatioEqSignatureIndex
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open GlobalTheory.RowLev GlobalTheory.RowLev.Inhab IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

namespace GlobalTheory.RowIndex

variable {I : AutInst}

theorem mem_mL {m : ℕ} {x : VA I} : x ∈ mL I m ↔ ∃ z ∈ I.Lf, x = (m : I.E ⊗[I.F] Af I.F) • z := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', rfl⟩ := hy
    exact ⟨z + z', add_mem hz hz', (smul_add _ _ _).symm⟩
  | smul a x _ hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨a • z, Submodule.smul_mem _ a hz, smul_comm (a : I.E ⊗[I.F] Af I.F) _ z⟩


end GlobalTheory.RowIndex
end

