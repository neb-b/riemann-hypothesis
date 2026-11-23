module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocalModelSliceTargetLine
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SliceModelT

variable {D : D7}

theorem resT_symm_left {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (u : WO S A) :
    (d.resT S).symm (u, 0) = GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank) u := by
  rw [OrthDec.resT_symm_apply, GlobalTheory.MixModel.sandwich_apply, Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem isThetaFunO_sliceT_left {ψ : AddChar (AF D.host.F) ℂ} {T A B S : HSp D} (d : OrthDec T A B) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (v : WO S B) : IsThetaFunO ψ S A fun u => f ((d.resT S).symm (u, v)) := {
  quasi γ u := by
    have e0 : (d.resT S).symm (ratW A S γ, 0) = ratW T S (d.iA * γ) := by
      rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, ratW_eq, ratW_eq, rat_mul]; rfl
    have e : ((ratW A S γ + u, v) : WO S A × WO S B) = (ratW A S γ, (0 : WO S B)) + (u, v) := by simp
    show f ((d.resT S).symm (ratW A S γ + u, v)) = ψ (-(symplOH S A (ratW A S γ) u)) * f ((d.resT S).symm (u, v))
    rw [e, map_add (f := _), e0, hf.quasi, ← e0, d.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      GlobalTheory.MixModel.symplOH_zero_left, add_zero]
  level := by
    obtain ⟨U, hU, hk⟩ := hf.level
    refine ⟨U.comap (GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank)),
      hU.preimage (GlobalTheory.MixModel.continuous_sandwich _ _), fun u hu h0 => ?_⟩
    funext w
    have e1 := congrFun (hk _ hu (GlobalTheory.MixModel.map_sandwich _ _ _ h0)) ((d.resT S).symm (w, v))
    rw [← resT_symm_left] at e1
    simp only [heisO] at e1 ⊢
    rw [← e1, ← map_add (d.resT S).symm, Prod.mk_add_mk, add_zero, d.symplOH_resT, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  cont := hf.cont.comp ((d.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const))
  smooth m L hL h0 w := by
    have e : ∀ t, (d.resT S).symm (w + L t, v) =
        (d.resT S).symm (w, v) + ((GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank)).comp L) t := by
      intro t
      rw [AddMonoidHom.comp_apply, ← resT_symm_left, ← map_add (d.resT S).symm, Prod.mk_add_mk, add_zero]
    simp only [e]
    exact hf.smooth m ((GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank)).comp L)
      ((GlobalTheory.MixModel.continuous_sandwich _ _).comp hL) (fun t => GlobalTheory.MixModel.map_sandwich _ _ _ (h0 t)) _ }

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

def prH : D.host.E →+* k := p.π.comp (incA D)

theorem ι_mul (a : AE D) (x : k) : p.ι (p.π a * x) = a * p.ι x := by
  have h1 : p.π a * x = p.π (a * p.ι x) := by rw [map_mul, p.π_ι]
  rw [h1, p.ι_π, mul_left_comm, ← p.ι_π, p.π_ι]

theorem mul_map_ι {m l n : Type} [Fintype l] (N : Matrix m l (AE D)) (M : Matrix l n k) :
    N * M.map p.ι = (N.map p.π * M).map p.ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul]

variable {ρ : ℕ} (B : BesLev D ρ) (S : HSp D) {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)} (FS : Frame k S.rank n)

theorem beta_eq (hF : p.IsCoreFrame B s FA F₀) :
    F₀.β = fromCols (B.o.iA.map (prH p) * FA.β) (Matrix.of fun r (_ : Unit) => s * prH p (vecB B.o B.ζ r)) := by
  ext r (a | _)
  · exact hF.1 r a
  · exact hF.2 r

theorem col_eq : (Matrix.of fun r (_ : Unit) => s * prH p (vecB B.o B.ζ r)) =
    s • (B.o.iB.map (prH p) * Matrix.of fun j (_ : Unit) => prH p (B.ζ j)) := by
  ext r u
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mul_apply, vecB, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem qA_beta (hF : p.IsCoreFrame B s FA F₀) : B.o.qA.map (prH p) * F₀.β = fromCols FA.β 0 := by
  rw [beta_eq p B hF, col_eq, Matrix.mul_fromCols, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.map_mul, ← Matrix.map_mul, B.o.qA_iA, B.o.qA_iB, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_zero _ (map_zero _), Matrix.one_mul, Matrix.zero_mul, smul_zero]

theorem up_fromRows (hF : p.IsCoreFrame B s FA F₀) (x : Matrix n' n k) :
    p.up FS F₀ (fromRows x 0) = (B.o.resT S).symm (p.up FS FA x, 0) := by
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Place.up, Place.up, OrthDec.jA, rat, mul_map_ι,
    beta_eq p B hF, fromCols_mul_fromRows, Matrix.mul_zero, add_zero, Matrix.map_map]
  simp only [Matrix.mul_assoc]
  rfl

theorem resT_up_fst (hF : p.IsCoreFrame B s FA F₀) (x : Matrix (n' ⊕ Unit) n k) :
    (B.o.resT S (p.up FS F₀ x)).1 = p.up FS FA x.toRows₁ := by
  rw [OrthDec.resT_apply]
  dsimp only
  rw [Place.up, Place.up, OrthDec.pA, rat, mul_map_ι, Matrix.map_map]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  change (B.o.qA.map (prH p) * F₀.β) * x * FS.γ = _
  rw [qA_beta p B hF]
  conv_lhs => rw [← fromRows_toRows x]
  rw [fromCols_mul_fromRows, Matrix.zero_mul, add_zero]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

def rowsH (n n' : Type) [Fintype n] [Fintype n'] : Matrix (n' ⊕ Unit) n k ≃ₜ Matrix n' n k × (n → k) where
  toFun x := (x.toRows₁, x (Sum.inr ()))
  invFun q := fromRows q.1 (Matrix.of fun _ => q.2)
  left_inv x := by
    ext (i | i) j <;> rfl
  right_inv q := by
    ext i j <;> rfl
  continuous_toFun := by
    refine Continuous.prodMk ?_ (continuous_apply _)
    exact continuous_pi fun i => continuous_apply (Sum.inl i)
  continuous_invFun := by
    refine continuous_pi fun i => ?_
    rcases i with i | i
    · exact (continuous_apply i).comp continuous_fst
    · exact continuous_snd

def tens (a : SB (n → k)) : SB (Matrix n' n k) →ₗ[ℂ] SB (Matrix (n' ⊕ Unit) n k) where
  toFun Ξ := GlobalTheory.LocFlat.CFac.comapH (rowsH n n') (GlobalTheory.LocFlat.CFac.prodSB Ξ a)
  map_add' Ξ Ξ' := by
    ext x
    simp [GlobalTheory.LocFlat.CFac.comapH_apply, GlobalTheory.LocFlat.CFac.prodSB_apply, add_mul]
  map_smul' c Ξ := by
    ext x
    simp [GlobalTheory.LocFlat.CFac.comapH_apply, GlobalTheory.LocFlat.CFac.prodSB_apply, mul_assoc]

theorem tens_apply (a : SB (n → k)) (Ξ : SB (Matrix n' n k)) (x : Matrix (n' ⊕ Unit) n k) :
    (tens a Ξ).1 x = Ξ.1 x.toRows₁ * a.1 (x (Sum.inr ())) := rfl

end GlobalTheory.SliceModelT


open GlobalTheory.SliceModelT in
theorem GlobalTheory.SliceModelT.main : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ FS F₀ T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO S B.L, ∃ T₁, p.IsModel ψ FS FA T₁ ∧ ∀ (Ξ : SB (Matrix n' n k)) (Ψ : SB (Matrix (n' ⊕ Unit) n k)), (∀ x, Ψ.1 x = Ξ.1 x.toRows₁ * a (x (Sum.inr ()))) → ∀ u, T₀ Ψ ((B.o.resT S).symm (u, v)) = T₁ Ξ u := by
  intro D k _ _ _ _ p ψ n n' _ _ _ _ ρ B S s FA F₀ FS hF T₀ hT a ha v
  let a' : SB (n → k) := ⟨a, ha⟩
  let T₁ : SB (Matrix n' n k) →ₗ[ℂ] (WO S B.A → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun u : WO S B.A => (B.o.resT S).symm (u, v))) ∘ₗ T₀ ∘ₗ tens a'
  have hT₁ : ∀ Ξ u, T₁ Ξ u = T₀ (tens a' Ξ) ((B.o.resT S).symm (u, v)) := fun _ _ => rfl
  refine ⟨T₁, ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun Ξ Ψ hΨ u => ?_⟩
  · exact isThetaFunO_sliceT_left B.o (hT.theta _) v
  · have h1 := hT.trans (fromRows x 0) (tens a' Φ) (tens a' Φ') (fun t => by
      have e1 : (t + fromRows x (0 : Matrix Unit n k)).toRows₁ = t.toRows₁ + x := by
        ext i j; simp [Matrix.toRows₁, Matrix.fromRows_apply_inl]
      have e2 : (t + fromRows x (0 : Matrix Unit n k) : Matrix (n' ⊕ Unit) n k) (Sum.inr ()) = t (Sum.inr ()) := by
        funext j; simp [Matrix.fromRows_apply_inr]
      rw [tens_apply, tens_apply, hΦ, e1, e2])
    funext u
    rw [hT₁, h1, up_fromRows p B S FS hF]
    simp only [heisO, hT₁]
    rw [← map_add (B.o.resT S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resT, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  · set Y : WO S B.V₀ := (B.o.resT S).symm (y, 0) with hYdef
    have hY : IsHalf (cA D p.e) Y := by
      intro i j
      rw [hYdef, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hy l j]
    have h1 := hT.modul Y hY (tens a' Φ) (tens a' Φ') (fun t => by
      rw [tens_apply, tens_apply, hΦ, B.o.symplO_resT, resT_up_fst p B S FS hF, hYdef, AddEquiv.apply_symm_apply,
        symplO_zero_right', add_zero, mul_assoc])
    funext u
    rw [hT₁, h1]
    simp only [heisO, hT₁]
    rw [← map_add (B.o.resT S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resT, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  · have e : Ψ = tens a' Ξ := Subtype.ext (funext hΨ)
    rw [e, hT₁]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlace
section
noncomputable section
open scoped TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_mul_gaMat (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one_gaMat (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem Place.pi_idem (p : Place D k) : p.π p.e = 1 := by
  have h1 := p.ι_π 1
  rw [mul_one, map_one] at h1
  rw [← h1, p.π_ι]

theorem Place.pi_eq_of_toEAf (p : Place D k) {a b : AE D} (h : toEAf D a = toEAf D b) : p.π a = p.π b := by
  have hf : finPart D a = finPart D b :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E).injective h
  have key : p.e * a = p.e * b := GlobalTheory.SplitScalar.adele_ext
    (by rw [map_mul, map_mul, GlobalTheory.SplitScalar.infPart_splitIdem p.split, zero_mul, zero_mul])
    (by rw [map_mul, map_mul, hf])
  calc p.π a = p.π (p.e * a) := by rw [map_mul, p.pi_idem, one_mul]
    _ = p.π (p.e * b) := by rw [key]
    _ = p.π b := by rw [map_mul, p.pi_idem, one_mul]

theorem Place.map_pi_eq_of_toEAf (p : Place D k) {m n : ℕ} {a b : Matrix (Fin m) (Fin n) (AE D)}
    (h : a.map (toEAf D) = b.map (toEAf D)) : a.map p.π = b.map p.π := by
  ext i j
  exact p.pi_eq_of_toEAf (congrFun (congrFun h i) j)

theorem exists_toEAf_lift (z : EAf D) : ∃ w : AE D, toEAf D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul b α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩

def liftM {m n : ℕ} (x : Matrix (Fin m) (Fin n) (EAf D)) : Matrix (Fin m) (Fin n) (AE D) :=
  x.map fun z => (exists_toEAf_lift z).choose

theorem liftM_map {m n : ℕ} (x : Matrix (Fin m) (Fin n) (EAf D)) : (liftM x).map (toEAf D) = x := by
  ext i j
  exact (exists_toEAf_lift (x i j)).choose_spec

def stdFrame (k : Type) [Field k] (N : ℕ) : Frame k N (Fin N) := ⟨1, 1, by simp, by simp⟩

theorem exists_GL_mul_of_mul_eq_one {n : ℕ} (M : GL (Fin n) k) (N Ni : Matrix (Fin n) (Fin n) k) (h : N * Ni = 1) :
    ∃ gk : GL (Fin n) k, gk.val = M.val * Ni := by
  have h' : Ni * N = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).1 h
  exact ⟨M * ⟨Ni, N, h', h⟩, rfl⟩

theorem Place.exists_movedTo (p : Place D k) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (M : GL (Fin V.rank) k) (g₀ : GA D V) : ∃ g, SuppAt p.e V g ∧ MovedTo p V (g * g₀) β M.val := by
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Matrix (Fin V.rank) (Fin V.rank) (AE D), b₀.map (toEAf D) = β.val :=
    ⟨liftM β.val, liftM_map _⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Matrix (Fin V.rank) (Fin V.rank) (AE D), c₀.map (toEAf D) = (β⁻¹).val :=
    ⟨liftM (β⁻¹).val, liftM_map _⟩
  have hbc : b₀.map p.π * c₀.map p.π = 1 := by
    rw [← Matrix.map_mul]
    have h1 : (b₀ * c₀).map (toEAf D) = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (toEAf D) := by
      rw [Matrix.map_mul, hb₀, hc₀, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul, mul_inv_cancel,
        Units.val_one]
    rw [p.map_pi_eq_of_toEAf h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hN : ((mt V g₀).map p.π * b₀.map p.π) * (c₀.map p.π * (mt V g₀⁻¹).map p.π) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (b₀.map p.π), hbc, Matrix.one_mul, ← Matrix.map_mul, ← mt_mul_gaMat,
      mul_inv_cancel, mt_one_gaMat, Matrix.map_one _ (map_zero _) (map_one _)]
  have hN' : (c₀.map p.π * (mt V g₀⁻¹).map p.π) * ((mt V g₀).map p.π * b₀.map p.π) = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).1 hN
  obtain ⟨gk, hgk⟩ := exists_GL_mul_of_mul_eq_one M _ _ hN
  obtain ⟨g, hg, -⟩ := ((_root_.GlobalTheory.LocGrp.local_groups D k p).1 V (Fin V.rank) (stdFrame k V.rank)).1 gk
  refine ⟨g, hg.1, fun b hb => ?_⟩
  have h2 : (mt V g).map p.π = gk.val := by
    rw [hg.2]
    change (1 : Matrix (Fin V.rank) (Fin V.rank) k) * gk.val * 1 = gk.val
    rw [Matrix.one_mul, Matrix.mul_one]
  have hbb : b.map p.π = b₀.map p.π := p.map_pi_eq_of_toEAf (by rw [hb, hb₀])
  rw [mt_mul_gaMat, Matrix.map_mul, Matrix.map_mul, h2, hbb, hgk, Matrix.mul_assoc (M.val * _), Matrix.mul_assoc M.val,
    hN', Matrix.mul_one]

theorem normalFrames_and_basePoint_exist : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k), p.xi ≠ 0 → (∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n), s ≠ 0 → (∃ F : Frame k B.V₀.rank (n ⊕ Unit), p.IsCoreFrame B s FA F) ∧ ∃ F : Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ (∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (J : JacLev D ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n), s ≠ 0 → hh ≠ 0 → ∃ F : Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F) ∧ ∀ (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (M : GL (Fin V.rank) k) (g₀ : GA D V), ∃ g, SuppAt p.e V g ∧ MovedTo p V (g * g₀) β M.val :=
  fun _ _ _ _ _ _ p _ =>
    ⟨fun _ _ _ _ B _ FA hs => ⟨p.exists_isCoreFrame hs B FA, p.exists_isBesFrame hs B FA⟩,
      fun _ _ _ _ J _ _ F₀ hs hh0 => p.exists_isJacFrame hs J hh0 F₀,
      fun V β M g₀ => p.exists_movedTo V β M g₀⟩

end GlobalTheory.LocMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPairSpaceLinearMapViaPartialFourier
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocFlat.CQLast

open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem eq_zero_of_hat_eq_zero (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (hne : ψ ≠ 1) {n : Type} [Fintype n] [DecidableEq n] {f : (n → k) → ℂ} (hf : f ∈ SB (n → k))
    (h0 : ∀ η, GlobalTheory.StepData.hat ψ ν (-1) f η = 0) (a : n → k) : f a = 0 := by
  classical
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨c, hc⟩ := (GlobalTheory.SplitWeil.conductor_exists k).1 ψ hψ hne
  set μ : Measure (n → k) := Measure.pi fun _ => ν with hμ
  have hF : ∀ y, ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = 0 := by
    intro y
    have h1 := h0 (-y)
    simp only [GlobalTheory.StepData.hat] at h1
    rw [← h1]
    congr 1
    funext x
    rw [neg_dotProduct, neg_one_mul, neg_neg, dotProduct_comm]
  set g : (n → k) → ℂ := fun x => f (x + a) with hgdef
  have hg : g ∈ SB (n → k) :=
    ⟨hf.1.comp_continuous (continuous_add_const a), hf.2.comp_homeomorph (Homeomorph.addRight a)⟩
  have hpsi : ∀ u v : k, (ψ (u + v) : ℂ) = ψ u * ψ v := fun u v => by
    rw [AddChar.map_add_eq_mul, Circle.coe_mul]
  have hpsi' : ∀ u : k, (ψ (-u) : ℂ) * ψ u = 1 := fun u => by
    rw [← hpsi, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
  have hG : ∀ y, ∫ x, g x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = 0 := by
    intro y
    have e : ∀ x, g x * (ψ (x ⬝ᵥ y) : ℂ) = (ψ (-(a ⬝ᵥ y)) : ℂ) * (f (x + a) * ψ ((x + a) ⬝ᵥ y)) := by
      intro x
      rw [add_dotProduct, hpsi, hgdef]
      linear_combination (f (x + a) * (ψ (x ⬝ᵥ y) : ℂ)) * (hpsi' (a ⬝ᵥ y)).symm
    simp_rw [e]
    rw [integral_const_mul, integral_add_right_eq_self (fun x => f x * (ψ (x ⬝ᵥ y) : ℂ)) a, hF, mul_zero]
  obtain ⟨s, hs⟩ := FourierPi.fourier_inversion_pi μ hc hg
  simp only [hG, integral_zero] at hs
  have hpos : ∀ r : kˣ, 0 < μ.real (FourierPi.box n r) := by
    intro r
    refine ENNReal.toReal_pos ((FourierPi.isOpen_box r).measure_pos μ ⟨0, ?_⟩).ne'
      (FourierPi.isCompact_box r).measure_lt_top.ne
    simp [FourierPi.box, cball]
  have h2 : g 0 = 0 := by
    rcases mul_eq_zero.1 hs.symm with h | h
    · exfalso
      have := mul_pos (hpos s) (hpos (c * s⁻¹))
      exact this.ne' (by exact_mod_cast h)
    · exact h
  simpa [hgdef] using h2

def withLast {n n' : Type} (x₀ : Matrix n n' k) (y : n → k) : Matrix n (n' ⊕ Unit) k :=
  fromCols x₀ (Matrix.of fun r (_ : Unit) => y r)

theorem withLast_toCols {n n' : Type} (x : Matrix n (n' ⊕ Unit) k) :
    withLast x.toCols₁ (fun r => x r (Sum.inr ())) = x := by
  ext r (j | u)
  · rfl
  · cases u; rfl

theorem continuous_withLast {n n' : Type} (x₀ : Matrix n n' k) : Continuous (withLast x₀) := by
  refine continuous_matrix fun i j => ?_
  rcases j with a | u
  · simp only [withLast, Matrix.fromCols_apply_inl]; exact continuous_const
  · simp only [withLast, Matrix.fromCols_apply_inr, Matrix.of_apply]; exact continuous_apply i

theorem slice_mem_SB {n n' : Type} [Fintype n] [Fintype n'] {Ψ : Matrix n (n' ⊕ Unit) k → ℂ}
    (hΨ : Ψ ∈ SB (Matrix n (n' ⊕ Unit) k)) (x₀ : Matrix n n' k) :
    (fun y : n → k => Ψ (withLast x₀ y)) ∈ SB (n → k) := by
  have := GlobalTheory.SplitWeil.t2Space k
  have hcl : Topology.IsClosedEmbedding (withLast x₀) :=
    Function.LeftInverse.isClosedEmbedding (f := fun x : Matrix n (n' ⊕ Unit) k => fun r => x r (Sum.inr ()))
      (fun y => rfl) (by fun_prop) (continuous_withLast x₀)
  exact ⟨hΨ.1.comp_continuous (continuous_withLast x₀), hΨ.2.comp_isClosedEmbedding hcl⟩

def partialHat (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ) (n n' : Type)
    [Fintype n] [Fintype n'] :
    SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (Matrix n n' k × (n → k) → ℂ) where
  toFun Ψ p := GlobalTheory.StepData.hat ψ ν (-1) (fun y => Ψ.1 (withLast p.1 y)) p.2
  map_add' Ψ Ψ' := by
    funext p
    simp only [GlobalTheory.StepData.hat, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (GlobalTheory.StepData.integrable_hat ψ ν (-1) hψ (slice_mem_SB Ψ.2 p.1) p.2)
      (GlobalTheory.StepData.integrable_hat ψ ν (-1) hψ (slice_mem_SB Ψ'.2 p.1) p.2)
  map_smul' a Ψ := by
    funext p
    simp only [GlobalTheory.StepData.hat, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact integral_const_mul a _

theorem partialHat_injective (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (hne : ψ ≠ 1) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] :
    Function.Injective (partialHat ν ψ hψ n n') := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Ψ h
  ext x
  have h1 := eq_zero_of_hat_eq_zero ν ψ hψ hne (slice_mem_SB Ψ.2 x.toCols₁)
    (fun η => congrFun h (x.toCols₁, η)) (fun r => x r (Sum.inr ()))
  simpa [withLast_toCols] using h1

def coupleBil (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ) (n n' Z : Type)
    [Fintype n] [Fintype n'] :
    SB (Matrix Z n k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (Matrix n n' k × Matrix (Z ⊕ Unit) n k → ℂ) :=
  LinearMap.mk₂ ℂ (fun g Ψ q => g.1 q.2.toRows₁ * partialHat ν ψ hψ n n' Ψ (q.1, q.2 (Sum.inr ())))
    (fun g g' Ψ => by funext q; simp [add_mul])
    (fun a g Ψ => by funext q; simp [mul_assoc])
    (fun g Ψ Ψ' => by funext q; simp [mul_add])
    (fun a g Ψ => by funext q; simp; ring)

theorem coupleBil_injective (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (hne : ψ ≠ 1) (n n' Z : Type) [Fintype n] [DecidableEq n] [Fintype n'] :
    Function.Injective (TensorProduct.lift (coupleBil ν ψ hψ n n' Z)) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  let b := Module.Free.chooseBasis ℂ (SB (Matrix Z n k))
  set c := TensorProduct.equivFinsuppOfBasisLeft b t with hc
  have ht' : t = c.sum fun i m => b i ⊗ₜ m := by
    rw [hc, ← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  have hm : ∀ (x₀ : Matrix n n' k) (η : n → k) (x : Matrix Z n k),
      ∑ i ∈ c.support, (b i).1 x * partialHat ν ψ hψ n n' (c i) (x₀, η) = 0 := by
    intro x₀ η x
    have hrow : (fromRows x (Matrix.of fun (_ : Unit) r => η r)) (Sum.inr ()) = η := by
      funext r; simp
    have := congrFun ht (x₀, fromRows x (Matrix.of fun (_ : Unit) r => η r))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ht', Finsupp.sum, map_sum, TensorProduct.lift.tmul] at this
    simpa [coupleBil, Finset.sum_apply, hrow] using this
  have hzero : c = 0 := by
    ext i : 1
    by_cases hi : i ∈ c.support
    · have hP : partialHat ν ψ hψ n n' (c i) = partialHat ν ψ hψ n n' 0 := by
        rw [map_zero]
        funext p
        have hli := (linearIndependent_iff'.mp b.linearIndependent) c.support
          (fun j => partialHat ν ψ hψ n n' (c j) p)
          (by
            ext x
            simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
              ZeroMemClass.coe_zero, Pi.zero_apply]
            rw [← hm p.1 p.2 x]
            exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)) i hi
        simpa using hli
      simpa using partialHat_injective ν ψ hψ hne n n' hP
    · simp [Finsupp.notMem_support_iff.mp hi]
  rw [ht', hzero]
  simp

theorem exists_pair_map : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ (n n' Z : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype Z] [DecidableEq Z] (M : Type) [AddCommGroup M] [Module ℂ M] (Bl : SB (Matrix Z n k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M), ∃ Λ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k) →ₗ[ℂ] M, (∀ (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ψ₂ : SB (Matrix Z n k)) (Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)), (∀ q, Ξ.1 q = Ψ₂.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => Ψ₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) (q.2 (Sum.inr ()))) → Λ Ξ = Bl Ψ₂ Ψ₁) ∧ ∀ (Ξ₁ : SB (Matrix n n' k)) (a : SB (Matrix Z n k)) (c : SB (Matrix n Unit k)) (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)), (∀ x, Ψ₁.1 x = Ξ₁.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → (∀ q, Ξ.1 q = Ξ₁.1 q.1 * (a.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (q.2 (Sum.inr ())))) → Λ Ξ = Bl a Ψ₁ := by
  intro k _ _ _ _ _ _ ν hν ψk hψ hne n n' Z _ _ _ _ _ _ M _ _ Bl
  classical
  set T := TensorProduct.lift (coupleBil ν ψk hψ n n' Z) with hT
  have hinj := coupleBil_injective ν ψk hψ hne n n' Z
  let eT := LinearEquiv.ofInjective T hinj
  let W : Submodule ℂ (SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)) :=
    (LinearMap.range T).comap (SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)).subtype
  let res : W →ₗ[ℂ] LinearMap.range T :=
    (SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)).subtype.restrict (fun x hx => hx)
  let Λ₀ : W →ₗ[ℂ] M := (TensorProduct.lift Bl).comp (eT.symm.toLinearMap.comp res)
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend Λ₀
  have key : ∀ (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ψ₂ : SB (Matrix Z n k))
      (Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k)), Ξ.1 = T (Ψ₂ ⊗ₜ Ψ₁) → Λ Ξ = Bl Ψ₂ Ψ₁ := by
    intro Ψ₁ Ψ₂ Ξ hΞ
    have hmem : Ξ ∈ W := ⟨Ψ₂ ⊗ₜ Ψ₁, hΞ.symm⟩
    have h1 := LinearMap.congr_fun hΛ ⟨Ξ, hmem⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1
    rw [h1]
    have h2 : res ⟨Ξ, hmem⟩ = eT (Ψ₂ ⊗ₜ Ψ₁) := Subtype.ext (by
      rw [LinearEquiv.ofInjective_apply]
      exact hΞ)
    simp only [Λ₀, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h2, LinearEquiv.symm_apply_apply,
      TensorProduct.lift.tmul]
  refine ⟨Λ, fun Ψ₁ Ψ₂ Ξ h => key Ψ₁ Ψ₂ Ξ (funext fun q => ?_),
    fun Ξ₁ a c Ψ₁ Ξ h1 h2 => key Ψ₁ a Ξ (funext fun q => ?_)⟩
  · rw [h q, hT, TensorProduct.lift.tmul]
    rfl
  · rw [h2 q, hT, TensorProduct.lift.tmul]
    have e : (fun y => Ψ₁.1 (withLast q.1 y)) = fun y => Ξ₁.1 q.1 * c.1 (Matrix.of fun r (_ : Unit) => y r) := by
      funext y
      rw [h1]
      rfl
    change _ = a.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => Ψ₁.1 (withLast q.1 y)) (q.2 (Sum.inr ()))
    rw [e]
    simp only [GlobalTheory.StepData.hat, mul_assoc]
    rw [integral_const_mul]
    ring

end GlobalTheory.LocFlat.CQLast
end
end

