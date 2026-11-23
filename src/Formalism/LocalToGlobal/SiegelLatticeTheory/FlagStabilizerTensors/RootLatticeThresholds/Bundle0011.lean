module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.Bundle0005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0041
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0009
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0007
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0013

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LatDictK

section DictK

variable {D : D7} (X : HidaSetting D)

def vOf (x : Fin X.B.I.n → X.B.I.E) : (VS D).V := ∑ i, X.ιE (x i) • X.bas i

theorem crd_vOf (x : Fin X.B.I.n → X.B.I.E) : X.crd (vOf X x) = x := by
  funext i
  simp only [HidaSetting.crd, crdOf, vOf]
  rw [X.bas.repr_sum_self]
  simp

theorem fmatK_inv_mul (x : X.B.I.Gf) : X.B.I.fmat x⁻¹ * X.B.I.fmat x = 1 := by
  show X.B.I.fmat (x⁻¹ * x) = 1
  simp [AutInst.fmat]

theorem fmatK_mul (x y : X.B.I.Gf) : X.B.I.fmat (x * y) = X.B.I.fmat x * X.B.I.fmat y := rfl

theorem dict_K (a b : X.B.I.Gf) (S : Set (VS D).V)
    (ha : ∀ y, y ∈ S ↔ X.B.I.fmat a⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf)
    (hb : ∀ y, y ∈ S ↔ X.B.I.fmat b⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf) : a⁻¹ * b ∈ X.B.I.Kset := by
  have hL : PIW.AdelClassFin.abelian₂ X.B.I a = PIW.AdelClassFin.abelian₂ X.B.I b := by
    ext v
    show X.B.I.fmat a⁻¹ *ᵥ PIW.AdelClassFin.iv X.B.I v ∈ X.B.I.Lf ↔
      X.B.I.fmat b⁻¹ *ᵥ PIW.AdelClassFin.iv X.B.I v ∈ X.B.I.Lf
    have e : PIW.AdelClassFin.iv X.B.I v = incl X.B.I (X.crd (vOf X v)) := by rw [crd_vOf]; rfl
    rw [e]
    exact (ha _).symm.trans (hb _)
  obtain ⟨k, hk, hkeq⟩ := PIW.AdelClassFin.lattice_map_injective X.B.I a b hL
  rw [hkeq, ← mul_assoc, inv_mul_cancel, one_mul]
  exact hk

end DictK

end LatDictK

open LatDictK

section DictKMain

variable {D : D7} (X : HidaSetting D)

theorem colLatK {u : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) :
    Formalism.L2.SG.NormCut.ColLatK cs := by
  intro ρ σ h
  refine dict_K X _ _ {y | y ∈ cs.lamOf ρ} (fun y => cs.lat_eq ρ y) (fun y => ?_)
  show y ∈ cs.lamOf ρ ↔ _
  rw [h]
  exact cs.lat_eq σ y

end DictKMain

namespace LatDictK

section DictK2

variable {D : D7} (X : HidaSetting D)

theorem ratLink_incl {x : X.B.I.GA} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h : RatLink X x γ) (w : (VS D).V) :
    X.B.I.fmat x.2 *ᵥ incl X.B.I (X.crd w) = incl X.B.I (X.crd (γ w)) := by
  obtain ⟨M, -, -, hf, hc⟩ := h
  have h3 : incl X.B.I ((M : Matrix _ _ _) *ᵥ X.crd w) =
      (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ incl X.B.I (X.crd w) := by
    funext i
    exact RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) (M : Matrix _ _ _) (X.crd w) i
  rw [hf, hc, h3]

theorem ratLink_incl_inv {x : X.B.I.GA} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h : RatLink X x γ) (y : (VS D).V) :
    X.B.I.fmat x.2⁻¹ *ᵥ incl X.B.I (X.crd y) = incl X.B.I (X.crd (γ.symm y)) := by
  conv_lhs => rw [← γ.apply_symm_apply y, ← ratLink_incl X h]
  rw [mulVec_mulVec, fmatK_inv_mul, one_mulVec]

end DictK2

end LatDictK

section DictKMain2

variable {D : D7} (X : HidaSetting D)

theorem termK {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows') :
    Formalism.L2.SG.NormCut.TermK F0 F0' cs cs' := by
  intro t
  obtain ⟨hRL, -, hmap, -⟩ := t.rep.2
  have hRL' : RatLink X t.pt t.lin := hRL
  have hmap' : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := hmap
  have hb0 := cs.base_lam t.lam t.mem
  have hb1 := cs'.base_lam t.lam' t.mem'
  have key : ((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)⁻¹ *
      (t.pt.2 * ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')) ∈ X.B.I.Kset := by
    refine dict_K X _ _ {y | y ∈ t.lam} (fun y => ?_) (fun y => ?_)
    · show y ∈ t.lam ↔ _
      conv_lhs => rw [← hb0]
      exact cs.lat_eq _ y
    · show y ∈ t.lam ↔ _
      have e1 : y ∈ t.lam ↔ t.lin.symm y ∈ t.lam' := by
        rw [← hmap']
        constructor
        · rintro ⟨z, hz, hzy⟩
          have : t.lin.symm y = z := by rw [← hzy]; simp
          rw [this]; exact hz
        · intro h
          exact ⟨t.lin.symm y, h, by simp⟩
      have hlat : ∀ w, w ∈ t.lam' ↔ X.B.I.fmat ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ *ᵥ
          incl X.B.I (X.crd w) ∈ X.B.I.Lf := fun w => by
        have := cs'.lat_eq (cs'.base t.lam') w
        rw [hb1] at this
        exact this
      rw [e1, hlat, show (t.pt.2 * ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u'))⁻¹ =
          ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * t.pt.2⁻¹ from _root_.mul_inv_rev _ _,
        fmatK_mul, ← mulVec_mulVec, ratLink_incl_inv X hRL']
  have e : kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt =
      ((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)⁻¹ *
        (t.pt.2 * ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')) := by
    simp only [kOf, mul_assoc]
  rw [e]
  exact key

end DictKMain2

namespace LatDictK

section DictK3

variable {D : D7} (X : HidaSetting D)

theorem nat_split (g : ℕ) : ∀ m : ℕ, 0 < m → ∃ c d : ℕ, m = c * d ∧ Nat.Coprime c g ∧ d ∣ g ^ m :=
  _root_.UpperTheory.Reformulated.B.ExistsCoprimeMulDvdPow.main g

theorem mem_of_loc {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (L : Submodule R M) (x : M)
    (h : ∀ Q : Ideal R, Q.IsMaximal → ∃ s, s ∉ Q ∧ s • x ∈ L) : x ∈ L := by
  let I : Ideal R := L.comap (LinearMap.toSpanSingleton R M x)
  by_cases hI : I = ⊤
  · have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    simpa [I] using h1
  · obtain ⟨Q, hQ, hIQ⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨s, hs, hsx⟩ := h Q hQ
    exact absurd (hIQ (show s ∈ I by simpa [I] using hsx)) hs

theorem crd_nsmul (n : ℕ) (v : (VS D).V) : X.crd (n • v) = n • X.crd v := by
  funext i
  simp [HidaSetting.crd, crdOf, map_nsmul]

theorem incl_nsmul (n : ℕ) (x : Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (n • x) = (n : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I x := by
  funext i
  simp [incl, nsmul_eq_mul]

end DictK3

end LatDictK

section DictKMain3

variable {D : D7} (X : HidaSetting D)

theorem modGAt : Formalism.L2.SG.NormCut.ModGAt X := by
  intro g1 Λ hΛ v hv
  have hg : X.B.g = gS D := X.g_eq
  obtain ⟨m, hm0, hm⟩ := PIW.AdelClassFin.lattice_denominator X.B.I (X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd v))
  have hmv : m • v ∈ Λ := by
    rw [hΛ, crd_nsmul, incl_nsmul, mulVec_smul]
    exact hm
  obtain ⟨c, d, hmcd, hcop, hdg⟩ := nat_split X.B.g m hm0
  have hcv : c • v ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ := by
    apply mem_of_loc
    intro Q hQ
    by_cases hgQ : ((gS D : ℕ) : 𝓞 D.host.E) ∈ Q
    · have hQ0 : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQ (NumberField.RingOfIntegers.not_isField _)
      obtain ⟨s, hs, hsv⟩ := hv ⟨Q, hQ.isPrime, hQ0⟩ hgQ
      refine ⟨s, hs, ?_⟩
      rw [smul_comm]
      exact Submodule.smul_of_tower_mem _ c hsv
    · refine ⟨((gS D * d : ℕ) : 𝓞 D.host.E), fun hQd => ?_, ?_⟩
      · rw [Nat.cast_mul] at hQd
        rcases hQ.isPrime.mem_or_mem hQd with h1 | h1
        · exact hgQ h1
        · obtain ⟨k, hk⟩ := hdg
          have h2 : ((X.B.g ^ m : ℕ) : 𝓞 D.host.E) ∈ Q := by
            rw [hk, Nat.cast_mul]; exact Q.mul_mem_right _ h1
          rw [Nat.cast_pow, hg] at h2
          exact hgQ (hQ.isPrime.mem_of_pow_mem _ h2)
      · have e : ((gS D * d : ℕ) : 𝓞 D.host.E) • (c • v) = ((gS D : ℕ) : 𝓞 D.host.E) • (m • v) := by
          rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, smul_smul, smul_smul, hmcd]
          ring_nf
        rw [e]
        exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hmv
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hcv
  obtain ⟨w, hw, hwv⟩ := hcv
  refine ⟨c, hcop, ?_⟩
  have e2 : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd v)) =
      (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd w)) := by
    rw [← mulVec_smul, ← mulVec_smul, ← incl_nsmul, ← incl_nsmul, ← crd_nsmul, ← crd_nsmul, ← hwv,
      Nat.cast_smul_eq_nsmul, hg]
  rw [e2]
  exact Submodule.subset_span ⟨_, (hΛ w).1 hw, rfl⟩

end DictKMain3

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEq
section
noncomputable section

open scoped Classical
open MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.LocJEq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem transp_mem (τ : D.what₂.Tau) {m : MatKR D.R.k D.R.rS} (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    C.Q τ * m * C.Qi τ ∈ UJset (X.B.I.ε (vOf X τ)) := by
  obtain ⟨-, h2, h3, -⟩ := C.isT τ
  have hm' : mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm
  show (C.Q τ * m * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * m * C.Qi τ) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ))
  calc (C.Q τ * m * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * m * C.Qi τ)
      = (C.Qi τ)ᴴ * (mᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * m) * C.Qi τ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ := by
        rw [h3, hm']
    _ = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
        rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

def Smap (τ : D.what₂.Tau) (γ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  Matrix.of.symm (C.Qi τ * umat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹)

theorem smap_cont (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : Continuous (Smap C τ γ) := by
  have hc : Continuous fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => umat (γ⁻¹ * z) :=
    (Units.continuous_val.comp continuous_subtype_val).comp (continuous_const.mul continuous_id)
  have h2 : Continuous fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      C.Qi τ * umat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹ :=
    ((continuous_const.matrix_mul hc).matrix_mul continuous_const).matrix_mul continuous_const
  exact h2

theorem sig_mul (τ : D.what₂.Tau) {a b : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ} (ha : a ∈ UJset (X.B.I.ε (vOf X τ)))
    (hb : b ∈ UJset (X.B.I.ε (vOf X τ))) (x : X.B.H (vOf X τ)) :
    X.B.σ (vOf X τ) (a * b) x = X.B.σ (vOf X τ) a (X.B.σ (vOf X τ) b x) := by
  rw [(X.ds (vOf X τ)).2.2.1.1.2 a ha b hb]
  rfl

theorem sig_one (τ : D.what₂.Tau) (x : X.B.H (vOf X τ)) : X.B.σ (vOf X τ) 1 x = x := by
  rw [(X.ds (vOf X τ)).2.2.1.1.1]
  rfl

theorem umat_mem (τ : D.what₂.Tau) (z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : umat z ∈ UJset (X.B.I.ε (vOf X τ)) := z.2

theorem QQi_left (τ : D.what₂.Tau) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) : C.Q τ * (C.Qi τ * M) = M := by
  rw [← Matrix.mul_assoc, (C.isT τ).2.1, Matrix.one_mul]

variable (hB : WuBessel C)

theorem wloc_eq (u : D.what₂.Word) (τ : D.what₂.Tau) (z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    X.Wloc u (vOf X τ) z = bOf hB u τ (X.B.σ (vOf X τ) (umat z) (X.B.w (vOf X τ))) :=
  (hB u τ).choose_spec.2 z

private theorem isUnit_det_y (τ : D.what₂.Tau) : IsUnit (C.y τ).det := by
  obtain ⟨h1, h2, h3, -⟩ := C.isT τ
  set J := Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) with hJdef
  have hy : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
  have hJ : J * J = 1 := by rw [hJdef, Formalism.REAL.Jm_mul_self]
  have hK : (C.Qi τ * J * (C.Qi τ)ᴴ) * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS = 1 := by
    rw [← h3]
    calc C.Qi τ * J * (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * J * C.Q τ)
        = C.Qi τ * (J * ((C.Q τ * C.Qi τ)ᴴ * (J * C.Q τ))) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, ← Matrix.mul_assoc J J, hJ, Matrix.one_mul, h1]
  refine Matrix.isUnit_det_of_left_inverse (B := C.Qi τ * J * (C.Qi τ)ᴴ * (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) ?_
  calc C.Qi τ * J * (C.Qi τ)ᴴ * (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ
      = (C.Qi τ * J * (C.Qi τ)ᴴ) * ((C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hy, hK]

theorem y_facts (τ : D.what₂.Tau) :
    C.Q τ * (C.y τ)⁻¹ * C.Qi τ ∈ UJset (X.B.I.ε (vOf X τ)) ∧ C.Q τ * C.y τ * C.Qi τ ∈ UJset (X.B.I.ε (vOf X τ)) ∧
      (C.Q τ * (C.y τ)⁻¹ * C.Qi τ) * (C.Q τ * C.y τ * C.Qi τ) = 1 := by
  have hu := isUnit_det_y C τ
  have hyi : (C.y τ)⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
    have hy : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
    have e1 : C.y τ * (C.y τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    show ((C.y τ)⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ)⁻¹ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
    calc ((C.y τ)⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ)⁻¹
        = ((C.y τ)⁻¹)ᴴ * ((C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ) * (C.y τ)⁻¹ := by rw [hy]
      _ = (C.y τ * (C.y τ)⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ * (C.y τ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by
          rw [e1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  refine ⟨transp_mem C τ hyi, transp_mem C τ (C.y_mem τ), ?_⟩
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  have e2 : (C.y τ)⁻¹ * C.y τ = 1 := Matrix.nonsing_inv_mul _ hu
  calc C.Q τ * (C.y τ)⁻¹ * C.Qi τ * (C.Q τ * C.y τ * C.Qi τ)
      = C.Q τ * ((C.y τ)⁻¹ * ((C.Qi τ * C.Q τ) * (C.y τ * C.Qi τ))) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [h1, Matrix.one_mul, ← Matrix.mul_assoc (C.y τ)⁻¹ (C.y τ), e2, Matrix.one_mul, h2]

theorem phi_def (u u' : D.what₂.Word) (τ : D.what₂.Tau) (m : MatKR D.R.k D.R.rS) :
    (locS hB u u' τ).Φ m = bOf hB u τ (X.B.σ (vOf X τ) (C.Q τ * m * C.Qi τ)
      (X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ)))) := rfl

theorem phi'_def (u u' : D.what₂.Word) (τ : D.what₂.Tau) (m : MatKR D.R.k D.R.rS) :
    (locS hB u u' τ).Φ' m = sclOf hB u u' τ • bOf hB u' τ (X.B.σ (vOf X τ) (C.Q τ * m * C.Qi τ)
      (X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ)))) := rfl

theorem phi_S (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z)) = X.Wloc u (vOf X τ) z := by
  obtain ⟨hy1, hy2, hy3⟩ := y_facts C τ
  have hg : uMat γ * umat γ⁻¹ = 1 := Units.mul_inv (γ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ)
  have hg' : ∀ M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, uMat γ * (umat γ⁻¹ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hg, Matrix.one_mul]
  have hM : C.Q τ * (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z)) * C.Qi τ =
      umat z * (C.Q τ * (C.y τ)⁻¹ * C.Qi τ) := by
    rw [show Matrix.of (Smap C τ γ z) = C.Qi τ * (umat γ⁻¹ * umat z) * C.Q τ * (C.y τ)⁻¹ from rfl]
    simp only [trG, Matrix.mul_assoc, QQi_left C τ, hg']
  have key : X.B.σ (vOf X τ) (C.Q τ * (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z)) * C.Qi τ)
      (X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ))) =
      X.B.σ (vOf X τ) (umat z) (X.B.w (vOf X τ)) := by
    rw [hM, sig_mul τ (umat_mem τ z) hy1, ← sig_mul τ hy1 hy2, hy3, sig_one τ]
  rw [phi_def C hB u u' τ, wloc_eq C hB u τ z, key]

theorem phi'_S (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (locS hB u u' τ).Φ' (Matrix.of (Smap C τ γ z)) = sclOf hB u u' τ • X.Wloc u' (vOf X τ) (γ⁻¹ * z) := by
  obtain ⟨hy1, hy2, hy3⟩ := y_facts C τ
  have hM : C.Q τ * Matrix.of (Smap C τ γ z) * C.Qi τ = umat (γ⁻¹ * z) * (C.Q τ * (C.y τ)⁻¹ * C.Qi τ) := by
    rw [show Matrix.of (Smap C τ γ z) = C.Qi τ * (umat γ⁻¹ * umat z) * C.Q τ * (C.y τ)⁻¹ from rfl]
    show _ = (umat γ⁻¹ * umat z) * _
    simp only [Matrix.mul_assoc, QQi_left C τ]
  have key : X.B.σ (vOf X τ) (C.Q τ * Matrix.of (Smap C τ γ z) * C.Qi τ)
      (X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ))) =
      X.B.σ (vOf X τ) (umat (γ⁻¹ * z)) (X.B.w (vOf X τ)) := by
    rw [hM, sig_mul τ (umat_mem τ (γ⁻¹ * z)) hy1, ← sig_mul τ hy1 hy2, hy3, sig_one τ]
  rw [phi'_def C hB u u' τ, wloc_eq C hB u' τ (γ⁻¹ * z), key]

theorem smulRight_smul {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] (a : V) (b : V') (c : ℂ) (hc : (starRingEnd ℂ) c = c) :
    (innerSL ℂ (c • b)).smulRight a = c • Formalism.L2.SG.TermOp.rk1 a b := by
  ext x
  simp [Formalism.L2.SG.TermOp.rk1, inner_smul_left, hc, smul_smul]

theorem locJ_map_eq (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))))
    (hG : AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of x))) (ν.map (Smap C τ γ))) :
    (locS hB u u' τ).J (ν.map (Smap C τ γ)) (trG (C.Q τ) (C.Qi τ) γ) =
      ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) •
        (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ)); Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) γ) := by
  have hc : (starRingEnd ℂ) (sclOf hB u u' τ) = sclOf hB u u' τ := by
    unfold sclOf; exact Complex.conj_ofReal _
  have hpt : ∀ z, (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of (Smap C τ γ z)))).smulRight
      ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z))) =
      sclOf hB u u' τ • Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) z) (X.Wloc u' (vOf X τ) (γ⁻¹ * z)) := by
    intro z
    rw [phi_S C hB, phi'_S C hB]
    exact smulRight_smul _ _ _ hc
  unfold LocS.J ampJ Jv Formalism.L2.SG.TermOp.OO
  rw [Measure.restrict_univ, integral_map (smap_cont C τ γ).measurable.aemeasurable hG,
    integral_congr_ae (ae_of_all _ hpt)]
  erw [integral_smul, smul_smul]
  rfl

def ujOf' {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M ∈ UJset ε) : Formalism.REAL.UJ ε :=
  ⟨⟨M, Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε, by
      have h : Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε * M = 1 := by
        have hM' : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε := hM
        rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM', Formalism.REAL.Jm_mul_self]
      rw [← Matrix.inv_eq_left_inv h]
      exact Matrix.mul_nonsing_inv M (Matrix.isUnit_det_of_left_inverse h), by
      have hM' : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε := hM
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM', Formalism.REAL.Jm_mul_self]⟩, hM⟩

theorem umat_ujOf' {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M ∈ UJset ε) :
    umat (ujOf' M hM) = M := rfl

theorem unit_det_y (τ : D.what₂.Tau) : IsUnit (C.y τ).det := isUnit_det_y C τ

theorem back_smap (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) :
    umat γ * (C.Q τ * (C.Qi τ * (umat γ⁻¹ * A) * C.Q τ * (C.y τ)⁻¹) * C.y τ * C.Qi τ) = A := by
  have hy : (C.y τ)⁻¹ * C.y τ = 1 := Matrix.nonsing_inv_mul _ (unit_det_y C τ)
  obtain ⟨-, h2, -, -⟩ := C.isT τ
  have hg : umat γ * umat γ⁻¹ = 1 := Units.mul_inv (γ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ)
  calc umat γ * (C.Q τ * (C.Qi τ * (umat γ⁻¹ * A) * C.Q τ * (C.y τ)⁻¹) * C.y τ * C.Qi τ)
      = umat γ * ((C.Q τ * C.Qi τ) * (umat γ⁻¹ * A) * C.Q τ * ((C.y τ)⁻¹ * C.y τ) * C.Qi τ) := by
        simp only [Matrix.mul_assoc]
    _ = A := by
        rw [h2, hy, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc (umat γ⁻¹ * A) (C.Q τ) (C.Qi τ), h2,
          Matrix.mul_one, ← Matrix.mul_assoc, hg, Matrix.one_mul]

theorem smap_val (τ : D.what₂.Tau) (γ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix.of (Smap C τ γ z) = C.Qi τ * (umat γ⁻¹ * umat z) * C.Q τ * (C.y τ)⁻¹ := by
  rfl

theorem range_smap (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Set.range (Smap C τ γ) =
      {x | umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ))} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    show umat γ * (C.Q τ * Matrix.of (Smap C τ γ z) * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ))
    rw [smap_val C τ γ z, back_smap C τ γ (umat z)]
    exact umat_mem τ z
  · intro hx
    have hx' : umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ)) := hx
    refine ⟨ujOf' _ hx', ?_⟩
    apply Matrix.of.injective
    rw [smap_val C τ γ (ujOf' _ hx'), umat_ujOf' _ hx']
    have hg : umat γ⁻¹ * umat γ = 1 := Units.inv_mul (γ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ)
    obtain ⟨h1, -, -, -⟩ := C.isT τ
    have hy : C.y τ * (C.y τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (unit_det_y C τ)
    calc C.Qi τ * (umat γ⁻¹ * (umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ))) * C.Q τ * (C.y τ)⁻¹
        = (C.Qi τ * C.Q τ) * Matrix.of x * (C.y τ * ((C.Qi τ * C.Q τ) * (C.y τ)⁻¹)) := by
          rw [← Matrix.mul_assoc (umat γ⁻¹) (umat γ), hg, Matrix.one_mul]
          simp only [Matrix.mul_assoc]
      _ = Matrix.of x := by
          rw [h1, Matrix.one_mul, Matrix.one_mul, hy, Matrix.mul_one]

end Formalism.L2.SG.Pf.LocJEq
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.UniformTheoremBOfLocalFrame
section
noncomputable section

namespace Formalism.L2.SG.Pf.BesselExpansion

open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.RotatedPoints Formalism.MainNotions.S.Pv.Frames

section Fr

variable (D : D7)

variable {D}

theorem gap_mono {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h h' : ℝ} (hg : GapAtLeast ε lam h) (hh : h' ≤ h) :
    GapAtLeast ε lam h' := fun a b hab => hh.trans (hg a b hab)

end Fr

end Formalism.L2.SG.Pf.BesselExpansion
end
end

