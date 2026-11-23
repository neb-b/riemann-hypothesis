module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bundle0004
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0079
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0044

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RhoSurjPf
section
noncomputable section

namespace Formalism.L2.SG.Pf.RhoSurjW

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.AdBridge PI.MassDataKppVolLemmas
  Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.AllRowsOf Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

section Loc

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem vecV_sub (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (a b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (a - b) = PI.FinKW.vecV X.B.I v a - PI.FinKW.vecV X.B.I v b := by
  funext i
  simp [PI.FinKW.vecV, map_sub]

theorem vecV_nsmul (v : HeightOneSpectrum (𝓞 X.B.I.F)) (c : ℕ)
    (a : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (c • a) = c • PI.FinKW.vecV X.B.I v a := by
  funext i
  simp [PI.FinKW.vecV]

theorem exists_cofactor (p : TypX X) : ∃ c : ℕ, (X.B.g : ℕ) = gOf p * c := by
  rw [X.g_eq]
  unfold gOf
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨D.host.g 0, mul_comm _ _⟩

theorem piV_mem_KgX (x : X.B.I.Gf) (hx : x ∈ X.B.I.Kg X.B.g) (p : TypX X) :
    piV X.B.I p.1 (tf X.B.I hb x) ∈ MassDataIdxSteps.KgX X p := by
  have hKf := (Bridge_mem_Kf_iff X.B.I hb x).2 hx.1
  rw [Kf, Subgroup.mem_iInf] at hKf
  refine ⟨hKf p.1, ?_⟩
  intro y hy
  obtain ⟨c, hc⟩ := exists_cofactor X p
  obtain ⟨u, huv, huw⟩ := PI.FinKW.local_vector_lift X.B.I p.1 y
  have huL : u ∈ X.B.I.Lf := PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective X.B.I u fun w => by
    by_cases hw : w = p.1
    · subst hw
      rw [huv]
      exact hy
    · rw [huw w hw]
      exact zero_mem _
  obtain ⟨z, hzL, hz⟩ := hx.2 u huL
  have hfx : X.B.I.fmat x = ofHAFin X.B.I (toHA X.B.I hb (1, x)) := (toHA_isBridge X.B.I hb (1, x)).2
  refine ⟨c • PI.FinKW.vecV X.B.I p.1 z, nsmul_mem (PI.FinKW.LocTo.mem_local_lattice_iff X.B.I z hzL p.1) c, ?_⟩
  have e := congrArg (PI.FinKW.vecV X.B.I p.1) hz
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, vecV_sub, hfx, PI.FinKW.vecV_mulVec, huv, Nat.cast_smul_eq_nsmul,
    vecV_nsmul] at e
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Nat.cast_smul_eq_nsmul, smul_smul, ← hc]
  exact e

end Loc

section Count

variable {D : D7} (X : HidaSetting D)

theorem card_target :
    Nat.card (∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) = Nat.card (G0g D.nd) := by
  classical
  have hT : (Nat.card (∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) : ℝ) =
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 0))) : ℝ) ^ D.R.f *
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 1))) : ℝ) ^ D.R.f := by
    rw [Nat.card_pi, Nat.cast_prod]
    rw [← Formalism.L2.SG.Pf.DstarIdxPf.prod_typ X (fun g => (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod g)) : ℝ))]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← Formalism.L2.SG.Pf.DstarIdxPf.ggC_eq D.R (gOf p)]
    rfl
  have hG : (Nat.card (G0g D.nd) : ℝ) =
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 0))) : ℝ) ^ D.R.f *
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 1))) : ℝ) ^ D.R.f := by
    rw [Nat.card_pi, Nat.cast_prod, Fintype.prod_sigma, Fin.prod_univ_two]
    have e : ∀ k : Fin 2, ∏ _v : D.nd.PlG k, (Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) : ℝ) =
        (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g k))) : ℝ) ^ D.R.f := fun k => by
      rw [Finset.prod_const, Finset.card_univ, D.nd.card_PlG]
      rfl
    exact congrArg₂ (· * ·) (e 0) (e 1)
  exact_mod_cast hT.trans hG.symm

end Count

theorem reduction_map_surjective : RhoSurj := by
  intro D X
  classical
  let hb : AdBridgeIso X.B.I := (Formalism.L2.SG.Closed.adelic_isomorphism_statement X.B.I).1
  have hK : ∀ p : TypX X, ((KvS X p : Subgroup _) : Set (MassDataIdxSteps.HAp X p)) = MassDataIdxSteps.KvX X p := by
    intro p
    obtain ⟨K, hKs, -, -, -⟩ := Formalism.L2.SG.Pf.MassDataX.stK_holds X p
    have e : KvS X p = K := by
      have e : (K : Set _) = Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1 := hKs
      rw [KvS, ← e, Subgroup.closure_eq]
    rw [e]
    exact hKs
  choose ρ hρ hker using fun p : TypX X => Formalism.L2.SG.Pf.MassDataX.stRed_holds X p (KvS X p) (hK p)
  let ψ : KsetSub X.B.I →* ∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)) :=
    (MonoidHom.pi fun p => (ρ p).comp (Pi.evalMonoidHom (fun p => KvS X p) p)).comp (phiK X hb)
  have hψ : Function.Surjective ψ := by
    intro t
    choose a ha using fun p => hρ p (t p)
    obtain ⟨k, hk⟩ := phiK_surjective X hb single_component_surjective a
    refine ⟨k, funext fun p => ?_⟩
    show ρ p (phiK X hb k p) = t p
    rw [hk]
    exact ha p
  let ι : KSub X.B.I → KsetSub X.B.I := fun x => ⟨x.1, x.2⟩
  have hψι : ∀ x y : KSub X.B.I, rhoX X x = rhoX X y → ψ (ι x) = ψ (ι y) := by
    intro x y hxy
    have h1 : rhoX X (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have hg := (rhoX_eq_one_iff X _).1 h1
    have h2 : ψ (ι (x⁻¹ * y)) = 1 := by
      funext p
      show ρ p (phiK X hb (ι (x⁻¹ * y)) p) = 1
      exact (hker p _).2 (RhoSurjW.piV_mem_KgX X hb _ hg p)
    have h3 : ι (x⁻¹ * y) = (ι x)⁻¹ * ι y := rfl
    rw [h3, map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have : ∀ k : Fin 2, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  let f : (rhoX X).range → (∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) :=
    fun r => ψ (ι (MonoidHom.mem_range.1 r.2).choose)
  have hf : Function.Surjective f := by
    intro t
    obtain ⟨k, hk⟩ := hψ t
    let x : KSub X.B.I := ⟨k.1, k.2⟩
    let r : (rhoX X).range := ⟨rhoX X x, x, rfl⟩
    exact ⟨r, (hψι _ x (MonoidHom.mem_range.1 r.2).choose_spec).trans hk⟩
  have hle : Nat.card (G0g D.nd) ≤ Nat.card (rhoX X).range := by
    rw [← RhoSurjW.card_target X]
    exact Nat.card_le_card_of_surjective f hf
  exact MonoidHom.range_eq_top.1 (Subgroup.eq_top_of_le_card _ hle)

end Formalism.L2.SG.Pf.RhoSurjW
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.StandardCoordinates
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.StandardCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (v : InfinitePlace X.B.I.F) {lam : ℂ} (hl : lam ≠ 0)
  {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ} {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ}
  (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (u' : D.what₂.Word)


include hT in
theorem fam_eq (hl : lam ≠ 0) (b : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.RealObj.frm X u' 1 v b =
      (lam ^ (D.R.rS - b.val))⁻¹ • (Q *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) b) := by
  unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
  refine Fin.lastCases ?_ (fun c => ?_) b
  · rw [Fin.snoc_last]
    unfold Formalism.QuantumDeterminants.fvec
    rw [dite_eq_right (by simp), Matrix.mulVec_mulVec, hT.2.1, Matrix.one_mulVec, Fin.val_last, Nat.sub_self, pow_zero,
      inv_one, one_smul]
  · rw [Fin.snoc_castSucc]
    have h1 := (hT.2.2.2 c c rfl).1
    unfold Formalism.QuantumDeterminants.fvec Formalism.QuantumDeterminants.bvec
    simp only [Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.eta]
    rw [h1, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl), one_smul]


include hT hl in
theorem stCoordV_gen (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (y : Formalism.REAL.UJ (X.B.I.ε v))
    (p : Formalism.L2.SG.RealObj.FreeE w) :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ v y p =
      ((D.host.rdE : ℂ) * lam) ^ (D.R.rS - p.1.1.1) / ((D.host.rdE : ℂ) * lam) ^ (D.R.rS - p.1.2.1) *
      ((Qi * uMat ((γ v)⁻¹ * y * γ v) * Q) *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) p.1.2)
        (Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨p.1.1.1, by have := p.2.1; have := p.1.2.isLt; omega⟩) := by
  have hQQi := hT.2.1
  have hH := hT.2.2.1
  have ha : p.1.1.1 < D.R.rS := by have := p.2.1; have := p.1.2.isLt; omega
  have hrd : (D.host.rdE : ℂ) ≠ 0 := by
    have := Formalism.L2.SG.RealFrameCoordinates.frS_mul_rd D
    intro h; rw [h, mul_zero] at this; exact zero_ne_one this
  set z' := Qi *ᵥ rv X.B.I v (X.zR u') with hz'
  set f := Formalism.QuantumDeterminants.fvec D.R.k D.R.rS z' p.1.2 with hf
  have hfrm : Formalism.L2.SG.RealObj.frm X u' D.host.rdE v p.1.2 =
      ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.2.val))⁻¹ • ((lam ^ (D.R.rS - p.1.2.val))⁻¹ • (Q *ᵥ f)) := by
    rw [← fam_eq v hT u' hl p.1.2]
    unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc
    simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
  have hfR : rv X.B.I v (X.fR ⟨p.1.1.1, ha⟩) =
      star (lam ^ (D.R.rS - p.1.1.1)) • (Q *ᵥ Pi.single (Formalism.QuantumDeterminants.esI D.R.k D.R.rS ⟨p.1.1.1, ha⟩) 1) := by
    rw [(hT.2.2.2 ⟨p.1.1.1, ha⟩ ⟨p.1.1.1, ha⟩ rfl).2, smul_smul, mul_inv_cancel₀, one_smul]
    exact star_ne_zero.2 (pow_ne_zero _ hl)
  have hM : uMat ((γ v)⁻¹ * y * γ v) *ᵥ (Q *ᵥ f) = Q *ᵥ ((Qi * uMat ((γ v)⁻¹ * y * γ v) * Q) *ᵥ f) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [← Matrix.mul_assoc Q, ← Matrix.mul_assoc Q, hQQi, Matrix.one_mul]
  have hQ : ∀ x v' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ,
      star (Q *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ (Q *ᵥ v')) = star x ⬝ᵥ (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS *ᵥ v') := by
    intro x v'
    rw [← Formalism.L2.SG.Pf.LTL.star_dot_conjT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH]
  unfold Formalism.L2.SG.NGPin.stCoordV
  rw [hfrm, hfR, Matrix.mulVec_smul, Matrix.mulVec_smul, hM]
  unfold hJ
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul, dotProduct_smul, star_smul, smul_dotProduct, hQ,
    Pi.star_single, star_one, single_dotProduct, one_mul, Formalism.L2.SG.RealFrameCoordinates.hpk_esI]
  simp only [smul_eq_mul, star_star]
  have h1 : (lam ^ (D.R.rS - p.1.2.val)) ≠ 0 := pow_ne_zero _ hl
  have h2 : ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.2.val)) ≠ 0 := pow_ne_zero _ hrd
  rw [mul_pow, mul_pow]
  field_simp


include hT hl in
theorem coord_conj (M H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)
    (hHU : Hᴴ * Formalism.REAL.Jm (X.B.I.ε v) * H = Formalism.REAL.Jm (X.B.I.ε v)) (hHu : IsUnit H.det)
    (he : ∀ b, H *ᵥ rv X.B.I v (X.eR b) = rv X.B.I v (X.eR b)) (hz : H *ᵥ rv X.B.I v (X.zR u') = rv X.B.I v (X.zR u'))
    (hfa : ∀ a, H *ᵥ rv X.B.I v (X.fR a) = rv X.B.I v (X.fR a)) (a : Fin D.R.rS) (b : Fin (D.R.rS + 1)) :
    ((Qi * (H⁻¹ * M * H) * Q) *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) b) (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) =
      ((Qi * M * Q) *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) b) (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) := by
  have hQQi := hT.2.1
  have hH := hT.2.2.1
  set f := Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) b with hf

  have hHf : H *ᵥ (Q *ᵥ f) = Q *ᵥ f := by
    have := fam_eq v hT u' hl b
    have e : Q *ᵥ f = lam ^ (D.R.rS - b.val) • Formalism.L2.SG.RealObj.frm X u' 1 v b := by
      rw [this, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hl), one_smul]
    rw [e, Matrix.mulVec_smul]
    congr 1
    unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
    simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
    refine Fin.lastCases ?_ (fun c => ?_) b
    · rw [Fin.snoc_last]; exact hz
    · rw [Fin.snoc_castSucc]; exact he c

  have hread : ∀ x : Fin X.B.I.n → ℂ, (Qi *ᵥ x) (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) =
      (lam ^ (D.R.rS - a.val))⁻¹ * hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) x := by
    intro x
    have hfR : rv X.B.I v (X.fR a) = star (lam ^ (D.R.rS - a.val)) • (Q *ᵥ Pi.single (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) 1) := by
      rw [(hT.2.2.2 a a rfl).2, smul_smul, mul_inv_cancel₀, one_smul]
      exact star_ne_zero.2 (pow_ne_zero _ hl)
    have hx : x = Q *ᵥ (Qi *ᵥ x) := by rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
    rw [hfR]
    conv_rhs => rw [hx]
    unfold hJ
    rw [star_smul, smul_dotProduct, ← Formalism.L2.SG.Pf.LTL.star_dot_conjT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH,
      Pi.star_single, star_one, single_dotProduct, one_mul, Formalism.L2.SG.RealFrameCoordinates.hpk_esI, smul_eq_mul, star_star,
      ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hl), one_mul]
  have hisom : ∀ x y : Fin X.B.I.n → ℂ, hJ (X.B.I.ε v) (H *ᵥ x) (H *ᵥ y) = hJ (X.B.I.ε v) x y := by
    intro x y
    unfold hJ
    rw [← Formalism.L2.SG.HermitianMatrixIdentities.star_dot_conjT' H x (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ (H *ᵥ y)), Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hHU]
  have hinvJ : ∀ x : Fin X.B.I.n → ℂ, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (H⁻¹ *ᵥ x) =
      hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) x := by
    intro x
    have hx : H *ᵥ (H⁻¹ *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hHu, Matrix.one_mulVec]
    rw [← hisom, hfa a, hx]
  have e1 : (Qi * (H⁻¹ * M * H) * Q) *ᵥ f = Qi *ᵥ (H⁻¹ *ᵥ (M *ᵥ (Q *ᵥ f))) := by
    simp only [← Matrix.mulVec_mulVec, hHf]
  have e2 : (Qi * M * Q) *ᵥ f = Qi *ᵥ (M *ᵥ (Q *ᵥ f)) := by
    simp only [← Matrix.mulVec_mulVec]
  rw [e1, e2, hread, hread, hinvJ]

end Formalism.L2.SG.StandardCoordinates

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.UMatMulInv
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
  (v : InfinitePlace X.B.I.F)

theorem map_span_G (g : Formalism.REAL.UJ (X.B.I.ε v)) (Fp : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ)
    (S : Set (Fin (D.R.rS + 1))) (y : Fin X.B.I.n → ℂ)
    (hy : y ∈ Submodule.span ℂ ((fun b => uMat g *ᵥ Fp b) '' S)) :
    uMat g⁻¹ *ᵥ y ∈ Submodule.span ℂ (Fp '' S) := by
  have e : Submodule.span ℂ ((fun b => uMat g *ᵥ Fp b) '' S) =
      (Submodule.span ℂ (Fp '' S)).map (Matrix.mulVecLin (uMat g)) := by
    rw [Submodule.map_span, Set.image_image]
    rfl
  rw [e] at hy
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
  have h1 : uMat g⁻¹ * uMat g = 1 := by simp [uMat]
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  exact hz

section Main

variable (hw : OkPt X u u' w)

def yU (c : FreeE w → ℂ) (hw : OkPt X u u' w) : Formalism.REAL.UJ (X.B.I.ε v) :=
  mkUJ _ (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c)) (yM_unit X u u' w v hw c)

theorem T_sub (c : FreeE w → ℂ) (x : Fin X.B.I.n → ℂ) :
    (uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v) - 1) *ᵥ x =
      uMat (gamW X u u' w v)⁻¹ *ᵥ (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) *ᵥ
        (uMat (gamW X u u' w v) *ᵥ x) - uMat (gamW X u u' w v) *ᵥ x) := by
  have hc : uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v) =
      uMat (gamW X u u' w v)⁻¹ * uMat (yU X u u' w v c hw) * uMat (gamW X u u' w v) := rfl
  have hy : uMat (yU X u u' w v c hw) = Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) := rfl
  have h1 : uMat (gamW X u u' w v)⁻¹ * uMat (gamW X u u' w v) = 1 := by simp [uMat]
  rw [hc, hy, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem G_eq (b : Fin (D.R.rS + 1)) : Gw X u u' w v b = uMat (gamW X u u' w v) *ᵥ frm X u' D.host.rdE v b := rfl

include hw in
theorem TG_comb (c : FreeE w → ℂ) (b : Fin (D.R.rS + 1)) :
    uMat (gamW X u u' w v)⁻¹ *ᵥ (Yc (X.B.I.ε v) (Fw X u v) (Gw X u u' w v) (Cw w c) *ᵥ Gw X u u' w v b -
      Gw X u u' w v b) = ∑ b', (Cw w c - 1) b' b • frm X u' D.host.rdE v b' := by
  have h1 : uMat (gamW X u u' w v)⁻¹ * uMat (gamW X u u' w v) = 1 := by simp [uMat]
  have hA : ∀ x, uMat (gamW X u u' w v)⁻¹ *ᵥ (uMat (gamW X u u' w v) *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [yM_G X u u' w v hw c b]
  simp only [G_eq, Matrix.mulVec_sub, Matrix.mulVec_sum, Matrix.mulVec_smul, hA, Matrix.sub_apply, sub_smul,
    Finset.sum_sub_distrib, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

include hw in
theorem inN_u' (c : FreeE w → ℂ) :
    InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))
      (uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v)) := by
  have hC := isUB_Cw w c
  refine ⟨⟨fun a => ?_, ?_⟩, fun x hx => ?_⟩
  · show (uMat ((gamW X u u' w v)⁻¹ * yU X u u' w v c hw * gamW X u u' w v) - 1) *ᵥ rv X.B.I v (X.eR a) ∈ _
    rw [T_sub, e_eq X u' v a, Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_sub, Matrix.mulVec_smul,
      ← G_eq, TG_comb X u u' w v hw c]
    exact Submodule.smul_mem _ _ (span_frm_le X u' v a.1 a.2.le (comb_mem X u' v hC a.castSucc))
  · rw [T_sub, ← frm_last X u' v, ← G_eq, TG_comb X u u' w v hw c]
    exact span_frm_le X u' v D.R.rS le_rfl (comb_mem X u' v hC (Fin.last D.R.rS))
  · rw [T_sub]
    have hperp := Yc_perpG _ _ _ (Tw u) (Tw u') (piW w) (blkW w) (gram_frm X v u _) (hGG_w X u u' w v) (piW_invol w)
      (piW_blk w) (piW_anti w) (hZ_w X u u' w hw v) (hgap_w X u u' w v hw) hC (uMat (gamW X u u' w v) *ᵥ x)
      (fun b hb => by
        obtain ⟨b0, rfl⟩ : ∃ b0 : Fin D.R.rS, b = b0.castSucc := ⟨⟨b.1, Fin.val_lt_last hb⟩, Fin.ext rfl⟩
        rw [G_eq, Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj (gamW X u u' w v), Matrix.mulVec_mulVec,
          Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul', Matrix.one_mulVec, frm_castSucc, hJs_l, hx b0, mul_zero])
    have h2 := map_span_G X v (gamW X u u' w v) (frm X u' D.host.rdE v) _ _ hperp
    rw [lt_last_set] at h2
    exact span_frm_le X u' v D.R.rS le_rfl h2

end Main

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

