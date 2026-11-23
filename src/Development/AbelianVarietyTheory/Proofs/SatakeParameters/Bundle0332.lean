module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0324
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmEmbeddingsEqOneOfInert
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0318
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
public import Formalism.LocalRingCardinality.HostCls
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPadicEmbeddingLeOneOfMemInverseHalfDifferent

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepCharacterAtLevelDetMulLocalCharacters
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopMuDet

open Matrix
open scoped TensorProduct

section Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_add {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a + b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  have hi : ∀ x : 𝓞 E, iA F E (algebraMap (𝓞 E) E x) ∈ Formalism.L2.Herm.intAf F E := fun x => (toRInt F E x).2
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a + b) =
      iA F E (algebraMap (𝓞 E) E r) * (iA F E (algebraMap (𝓞 E) E s) * a) +
        iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact add_mem (mul_mem (hi r) h1) (mul_mem (hi s) h2)

theorem intAtA_mul {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a * b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a * b) =
      (iA F E (algebraMap (𝓞 E) E s) * a) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact mul_mem h1 h2

theorem intAtA_int (x : 𝓞 E) : IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E x)) :=
  ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [map_one, map_one, one_mul]; exact (toRInt F E x).2⟩

def intAtSub (P : HeightOneSpectrum (𝓞 E)) :
    Subring (E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | IntAtA (F := F) P a}
  mul_mem' := intAtA_mul
  one_mem' := by simpa using intAtA_int (F := F) (P := P) 1
  add_mem' := intAtA_add
  zero_mem' := by simpa using intAtA_int (F := F) (P := P) 0
  neg_mem' := by
    intro a ha
    have := intAtA_mul (intAtA_int (F := F) (P := P) (-1)) ha
    simpa using this

theorem det_congAt {d : ℕ} (hd : 1 ≤ d) {k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h : CongAt P d k) :
    IntAtA (F := F) P (iA F E ((qOf P : ℕ) : E)⁻¹ *
      (((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) - 1)) := by
  classical
  set S := intAtSub (F := F) P with hS
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set Q := iA F E ((qOf P : ℕ) : E) with hQ
  have hcQ : iA F E ((qOf P : ℕ) : E)⁻¹ * Q = 1 := by rw [hQ, ← map_mul, inv_mul_cancel₀ hq, map_one]
  have hQS : Q ∈ S := by
    have := intAtA_int (F := F) (P := P) ((qOf P : ℕ) : 𝓞 E)
    simpa [hQ] using this
  have hZ : ∀ a b, Q ^ (d - 1) * (iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ *
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b) ∈ S :=
    fun a b => S.mul_mem (S.pow_mem hQS _) (h a b)
  have hZe : ∀ a b, Q * (Q ^ (d - 1) * (iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ *
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b)) =
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b := by
    intro a b
    have e : Q * Q ^ (d - 1) * iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hd, hQ, ← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
    rw [← mul_assoc, ← mul_assoc, e, one_mul]
  let Z : Matrix (Fin N) (Fin N) S := fun a b => ⟨_, hZ a b⟩
  let q' : S := ⟨Q, hQS⟩
  let M : Matrix (Fin N) (Fin N) S := 1 + q' • Z
  have hM : M.map S.subtype = (k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
    ext a b
    have e1 : S.subtype ((1 : Matrix (Fin N) (Fin N) S) a b) = (1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [Matrix.map_apply]
    simp only [M]
    rw [Matrix.add_apply, map_add (f := _), e1, Matrix.smul_apply, smul_eq_mul, map_mul]
    show _ + Q * (Q ^ (d - 1) * _) = _
    rw [hZe, Matrix.sub_apply]
    ring_nf
  set I : Ideal S := Ideal.span {q'}
  have hMI : M.map (Ideal.Quotient.mk I) = 1 := by
    ext a b
    have hq0 : Ideal.Quotient.mk I q' = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rw [Matrix.map_apply]
    simp only [M]
    rw [Matrix.add_apply, map_add (f := _), Matrix.smul_apply, smul_eq_mul, map_mul, hq0, zero_mul, add_zero,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, map_one]
    show (M.map (Ideal.Quotient.mk I)).det = 1
    rw [hMI, Matrix.det_one]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hdet)
  have hk : ((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      S.subtype M.det := by
    rw [RingHom.map_det, Matrix.GeneralLinearGroup.val_det_apply]
    exact congrArg Matrix.det hM.symm
  have e2 : iA F E ((qOf P : ℕ) : E)⁻¹ *
      (((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) - 1) = (w : _) := by
    rw [hk, show S.subtype M.det - 1 = S.subtype (M.det - 1) by simp, ← hw, map_mul]
    show iA F E ((qOf P : ℕ) : E)⁻¹ * ((w : _) * Q) = _
    rw [mul_comm (w : E ⊗[F] FiniteAdeleRing (𝓞 F) F), ← mul_assoc, hcQ, one_mul]
  rw [e2]
  exact w.2

end Cong

section Rat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem det_ratA (g : GL (Fin n) E) :
    ((Matrix.GeneralLinearGroup.det (ratA F g) : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      iA F E ((Matrix.GeneralLinearGroup.det g : Eˣ) : E) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

end Rat

section Frame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Fields} (s : Seam D X)

theorem det_seamGL {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) :
    ((Matrix.GeneralLinearGroup.det (seamGL s g) : D.host.Eˣ) : D.host.E) = s.iE ((LinearEquiv.det g : X.Eˣ) : X.E) := by
  have h : ((seamGL s g : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) =
      (LinearMap.toMatrix' g.toLinearMap).map (s.iE : X.E →+* D.host.E) := rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, LinearMap.det_toMatrix',
    LinearEquiv.coe_det]
  rfl

variable {i : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ)

theorem det_inFrame {P : SB} {κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)} (hd : 1 ≤ dep P) (h : InFrame s fb dep P κ g) :
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)) - 1)) := by
  have H := det_congAt hd h
  have e : ((Matrix.GeneralLinearGroup.det (((ratA D.host.F (fb P))⁻¹ * κ * ratA D.host.F (fb P))⁻¹ *
      ratA D.host.F (seamGL s g)) : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) =
      (((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)) := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, Units.val_mul, det_ratA, det_seamGL]
    congr 2
    rw [mul_comm, mul_inv_cancel_left]
  rw [← e]
  exact H

end Frame

end GlobalTheory.TopMuDet

end

theorem GlobalTheory.TwTop.muOf_det_top : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU →
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U)
    (g : SB t μ → (Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1)))) (z : SB t μ → t.X.K)
    (g' : SB t μ → (Sp t.X.E (D.R.N (t.m2 + 1 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1 + 1)))) (z' : SB t μ → t.X.K),
    (∀ P, A.cplRel β P (g P) (z P) ∧ InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 (g P)) →
    (∀ P, TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P (g' P) (z' P) ∧
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 (g' P)) →
    muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) *
        t.seam.σ₀ (∏ P, rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E) *
          rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E)) =
      muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ'.1)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hMu hi β β' κ κ' g z g' z' hg hg'
  have hlt : t.m2 + 1 < D.R.m := by omega
  have hok := (t.idx_ok μ).cst_ok
  obtain ⟨h1, -⟩ := GlobalTheory.T.muCharacter_det_level_eq_local_tame_product A dtU a hPin hTie hMu (t.m2 + 1) hlt (t.m2 + 1) (Nat.le_of_succ_le hi) β κ
    (fun P => ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E))
    (fun P => GlobalTheory.TopMuDet.det_inFrame t.seam _ _ (hok.D_pos P) (hg P).2)
  have hdep : ∀ P : SB t μ, 1 ≤ topDep t.sel (t.tup μ) (t.cst μ) P := by
    intro P
    unfold topDep
    split_ifs
    · exact le_rfl
    · have := hok.M_pos
      omega
  obtain ⟨-, h2⟩ := GlobalTheory.T.muCharacter_det_level_eq_local_tame_product A dtU a hPin hTie hMu (t.m2 + 1) hlt (t.m2 + 1 + 1) hi β' κ'
    (fun P => ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E))
    (fun P => GlobalTheory.TopMuDet.det_inFrame t.seam _ _ (hdep P) (hg' P).2)
  rw [Finset.prod_mul_distrib, map_mul, ← mul_assoc, h1, one_mul, h2]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelBadPrimesCoprimeResidueChar
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.SBad

theorem not_both_mem {R : Type*} [CommRing R] {I : Ideal R} (hI : I ≠ ⊤) {a b : ℕ} (h : Nat.Coprime a b)
    (ha : (a : R) ∈ I) (hb : (b : R) ∈ I) : False := by
  obtain ⟨s, r, hsr⟩ := h.cast (R := R)
  exact hI ((Ideal.eq_top_iff_one _).2 (hsr ▸ I.add_mem (I.mul_mem_left _ ha) (I.mul_mem_left _ hb)))

theorem mem_of_mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A}
    (h : P ∈ Formalism.L2.Col.divs a) : a ∈ P.asIdeal := by
  unfold Formalism.L2.Col.divs at h
  split_ifs at h with hf
  · simpa using h
  · simp at h

theorem coprime_absNorm_of_notMem {E : Type} [Field E] [NumberField E] (p : ℕ) [Fact p.Prime]
    (P : HeightOneSpectrum (𝓞 E)) (h : ((p : ℕ) : 𝓞 E) ∉ P.asIdeal) : Nat.Coprime (Ideal.absNorm P.asIdeal) p := by
  refine GlobalTheory.NormUnitInert.Arith.coprime_absNorm p P.ne_bot ?_
  refine P.isMaximal.out.2 _ (lt_of_le_of_ne le_sup_left fun he => h ?_)
  rw [he]
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}

theorem notMem_Sall (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (p : ℕ) (hp : p.Prime)
    (hTp : Nat.Coprime (D.mem u).A.T p) (hgp : ∀ i, p ≠ D.host.g i) (hQ : p ∉ Dx.Qp μ)
    (P : HeightOneSpectrum (𝓞 t.X.E)) (hP : P ∈ Formalism.L2.Col.Sall t.sel (t.tup μ) (t.word u)) :
    ((p : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal := by
  intro hpP
  simp only [Formalism.L2.Col.Sall, Formalism.L2.Col.rowSG, Formalism.L2.Col.uSG, Formalism.L2.Col.Primes.vGs, Finset.mem_union] at hP
  have hG : ∀ i, P ∈ t.Pr.vG i → False := fun i hPi => by
    have hc := mem_of_mem_divs hPi
    have hgm : ((D.host.g i : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
      rw [← t.g_rec i, ← t.pr_ok.piG_norm]
      exact Ideal.mul_mem_left _ _ hc
    have hgi : (D.host.g i).Prime := t.g_rec i ▸ t.pr_ok.g_prime i
    exact not_both_mem P.isPrime.ne_top ((Nat.coprime_primes hgi hp).2 (hgp i).symm) hgm hpP
  rcases hP with hP | (hP | hP) | hP
  · have hpi := mem_of_mem_divs hP
    have hTm : (((D.mem u).A.T : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
      rw [← t.T_rec u, ← t.pr_ok.piT_norm]
      exact Ideal.mul_mem_right _ _ hpi
    exact not_both_mem P.isPrime.ne_top hTp hTm hpP
  · exact hG 0 hP
  · exact hG 1 hP
  · exact hQ ((t.Q_rec μ p).2 ⟨hp, P, hP, hpP⟩)


set_option maxHeartbeats 1000000 in
theorem bad_prime_to_p : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => Nat.Coprime (t.rd u μ).lev (D.what₂.places.resChar w) ∧ (∀ Q ∈ GlobalTheory.TwU.ssRec t u μ, (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ (∀ v ∈ Formalism.L2.Col.plUnder D.host.F (GlobalTheory.TwU.ssRec t u μ), (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) ∧ ∀ v, GlobalTheory.TwU.UnderSB t μ v → (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X hF std t J S _ _
  classical
  have hp : (D.what₂.places.resChar w).Prime := hF.out
  obtain ⟨-, -, hTp, hgp⟩ := GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg
  have hSS := (t.rd_chain u μ).1
  have hlev := (t.rd_chain u μ).2.1
  have key := fun P hP => notMem_Sall t u μ _ hp hTp hgp J.away P hP
  have keyE : ∀ Q ∈ GlobalTheory.TwU.ssRec t u μ, (((D.what₂.places.resChar w : ℕ)) : 𝓞 D.host.E) ∉ Q.asIdeal := by
    intro Q hQ hm
    obtain ⟨P, hP, rfl⟩ := Finset.mem_map.1 hQ
    refine key P (hSS ▸ hP) ((GlobalTheory.TwU.mem_seamP t.seam P _).1 ?_)
    rw [map_natCast]
    exact hm
  have keyF : ∀ v ∈ Formalism.L2.Col.plUnder D.host.F (GlobalTheory.TwU.ssRec t u μ),
      (((D.what₂.places.resChar w : ℕ)) : 𝓞 D.host.F) ∉ v.asIdeal := by
    rintro v ⟨Q, hQ, hv⟩ hm
    rw [hv, Ideal.mem_comap, map_natCast] at hm
    exact keyE Q hQ hm
  refine ⟨?_, keyE, keyF, ?_⟩
  · rw [hlev]
    have hq : ∀ P : Formalism.L2.Col.rowSG t.Pr t.sel (t.tup μ), Nat.Coprime (Formalism.L2.Col.qOf P.1) (D.what₂.places.resChar w) :=
      fun P => coprime_absNorm_of_notMem _ P.1 (key P.1 (Finset.mem_union_right _ P.2))
    have hprod : Nat.Coprime (∏ P : Formalism.L2.Col.rowSG t.Pr t.sel (t.tup μ), Formalism.L2.Col.qOf P.1) (D.what₂.places.resChar w) :=
      Nat.Coprime.prod_left fun P _ => hq P
    have hT' : Nat.Coprime (t.Pr.T (t.word u)) (D.what₂.places.resChar w) := by rw [t.T_rec u]; exact hTp
    simp only [Formalism.L2.Ker.levC, Formalism.L2.Col.cAof, Formalism.L2.Col.cBof]
    exact Nat.Coprime.mul_left (Nat.Coprime.pow_left _ hprod) (Nat.Coprime.mul_left hT' (Nat.Coprime.pow_left _ hprod))
  · rintro v ⟨P, hP, hv⟩ hm
    rw [hv, Ideal.mem_comap, map_natCast] at hm
    refine key P (Finset.mem_union_right _ hP) ((GlobalTheory.TwU.mem_seamP t.seam P _).1 ?_)
    rw [map_natCast]
    exact hm

end GlobalTheory.TwV.Xc.SBad

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPolynomialOddDegreeOfRealisesFramePoly
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem blk_iff_posJ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ)
    (x : Var (X.Pj j)) (b : Σ v : X.Pl, Fin (X.G.P.n' v)) :
    ((⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj j).nV, Fin ((X.Pj j).n' v)) = (GlobalTheory.TwV.DelA.posJ X D pos j).symm (pos b)) ↔ blkJ X j x = b := by
  cases j
  · simp only [blkJ, idxJ]
    change _ = pos.symm (pos b) ↔ _
    rw [Equiv.symm_apply_apply]
    exact Iff.rfl
  · simp only [blkJ, idxJ]
    change _ = pos.symm (pos b) ↔ _
    rw [Equiv.symm_apply_apply]
    exact Iff.rfl

theorem oddDeg_of_realises : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → OddDeg X j G := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ Gc G hR hmap m hm b hb
  have hs : G.support = Gc.support := by
    rw [← MvPolynomial.support_map_of_injective G (algebraMap X.G.Kf Kc).injective, hmap,
      MvPolynomial.support_map_of_injective Gc ι.injective]
  rw [hs] at hm
  have hh := _root_.GlobalTheory.TwV.DelA.BlockHom.realises_blockHom X D pos j (rkS X D hN) (wT X D pos j) ν Q Gc hQ hR m hm (pos b)
  obtain ⟨he, -⟩ := _root_.GlobalTheory.TwV.DelA.eT_last_pair X D pos j (pos b)
  obtain ⟨-, hsz, -, -, -⟩ := _root_.GlobalTheory.TwV.DelA.size_first_last_rows X D pos j hN ν hν
  have hodd : IsOddPos (pos.symm (pos b)).2 := by rw [Equiv.symm_apply_apply]; exact hb
  rw [if_pos hodd] at he hh
  rw [he, ← hsz] at hh
  have hl : ((∑ x ∈ Finset.univ.filter (fun x => blkJ X j x = b), m x : ℕ) : ℤ) =
      ∑ x : Var (X.Pj j), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj j).nV, Fin ((X.Pj j).n' v)) = (GlobalTheory.TwV.DelA.posJ X D pos j).symm (pos b)
        then (m x : ℤ) else 0 := by
    rw [Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [blk_iff_posJ]
  have h1 : szT X D pos j (pos b) = szMu X j b.1 b.2 := by unfold szT; rw [Equiv.symm_apply_apply]
  have h2 : cT1 X D pos j (pos b) = cMu X j b.1 b.2 := by unfold cT1; rw [Equiv.symm_apply_apply]
  rw [hl, hh, h1, h2, hN.1]
  ring

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedPairDatumDependsOnlyOnLevel
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

namespace GlobalTheory.TwU

theorem xiM_datLoc : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), J.Dict std → ∀ j < (sysS H X std).mm, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La') := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J S hD j hjm La La' hLa hLa'
  have hm : (sysS H X std).mm = D.R.m := by
    first | rfl | exact X.fl_m
  have hj : j + 1 ≤ D.R.m := by omega
  obtain ⟨⟨h1, -⟩, -, hK1, -⟩ := hD j (Nat.le_of_succ_le hj) La hLa
  obtain ⟨⟨h2, -⟩, -, hK2, -⟩ := hD (j + 1) hj La' hLa'
  have hx : xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' = fun z =>
      S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La)
        (J.pt std (j + 1) hj La') (homRe h1 h2 z) := by
    funext z
    exact _root_.GlobalTheory.TwV.moved_pair_datum_eq_adelic_datum_alt t std J S.Xi j hj h1 h2 La La' z
  rw [hx]
  exact datLoc_homRe D t.cc (ssRec t u μ) (t.rd u μ).lev h1 h2 _ _ _ _ _ hK1 hK2
    (S.law.loc j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La)
      (J.pt std (j + 1) hj La'))

end GlobalTheory.TwU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormCmEmbeddingNormOneLocalUnitEqOne
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.UnitPos

theorem norm_twG_le {p : ℕ} [Fact p.Prime] (X : Sys p) (E : CEmbC X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (y : X.G.P.W v) :
    ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) y)‖ ≤ 1 := by
  have h := E.compat v s.val y
  have e : twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) y) =
      E.iK (X.G.P.ι v ((X.G.P.σ v ^ s.val) (algebraMap (X.G.P.W v) (X.G.P.Qq v) y))) := rfl
  rw [e, h, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap]
  exact Formalism.L2.G.Pend.norm_wToC_le p _

theorem norm_twG_unit {p : ℕ} [Fact p.Prime] (X : Sys p) (E : CEmbC X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (y : (X.G.P.W v)ˣ) :
    ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) (y : X.G.P.W v))‖ = 1 := by
  have h1 := norm_twG_le X E v s (y : X.G.P.W v)
  have h2 := norm_twG_le X E v s ((y⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have hm : twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) (y : X.G.P.W v)) *
      twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((y⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have hn := congrArg norm hm
  rw [norm_mul, norm_one] at hn
  have h0 : 0 ≤ ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) (y : X.G.P.W v))‖ := norm_nonneg _
  have h0' : 0 ≤ ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((y⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v))‖ := norm_nonneg _
  nlinarith

end GlobalTheory.TwV.UnitPos

namespace GlobalTheory.TwV.UnitPos

theorem embT_mem_qbar (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom

end GlobalTheory.TwV.UnitPos


open GlobalTheory.TwV.UnitPos in
theorem GlobalTheory.TwV.UnitPos.norm_embT_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ b : D.host.E, b * D.host.conj b = 1 → (∀ v, ∃ y : ((sysS H X std).G.P.W v)ˣ, J.rho std v b = algebraMap _ _ (y : (sysS H X std).G.P.W v)) → ∀ τ, ‖ι (TaylorLogMetric.embT D τ b)‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hS ι hι b hb hloc τ
  obtain ⟨⟨v, s⟩, rfl⟩ := (hT.gat_pos u w hg).surjective τ
  have hq := embT_mem_qbar D ((hT.gat_pos u w hg) ⟨v, s⟩) b
  have e1 : ι (TaylorLogMetric.embT D ((hT.gat_pos u w hg) ⟨v, s⟩) b) = TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D ((hT.gat_pos u w hg) ⟨v, s⟩) b) := by
    rw [TaylorLogMetric.lamC, dite_eq_left hq]
    exact hι ⟨_, hq⟩
  rw [e1, hS v s b]
  obtain ⟨y, hy⟩ := hloc v
  split_ifs with ho
  · have hc : J.rho std v (D.host.conj b) = algebraMap _ _ (((y⁻¹ : ((sysS H X std).G.P.W v)ˣ)) : (sysS H X std).G.P.W v) := by
      have h1 : J.rho std v (D.host.conj b) * J.rho std v b = 1 := by
        rw [← map_mul, mul_comm, hb, map_one]
      have h2 : algebraMap ((sysS H X std).G.P.W v) ((sysS H X std).G.P.Qq v) (((y⁻¹ : ((sysS H X std).G.P.W v)ˣ)) : (sysS H X std).G.P.W v) *
          J.rho std v b = 1 := by
        rw [hy, ← map_mul, Units.inv_mul, map_one]
      have hne : J.rho std v b ≠ 0 := by
        intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1
      exact mul_right_cancel₀ hne (h1.trans h2.symm)
    rw [hc]
    exact norm_twG_unit _ S.E v s _
  · rw [hy]
    exact norm_twG_unit _ S.E v s y
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormDerivationGeneratorsEqOneAtSite
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.EigenGenerator in
theorem GlobalTheory.TwV.DelB.dgen_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ τ, ‖ι ((t.O u μ).dgen τ)‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S ι hι τ
  have h5 := hg.2.1
  have hc := hg.2.2.1
  have hk := (primeClass_eq_inert_iff D.host.toHostRaw).1 hc
  have h2 : D.what₂.places.resChar w ∉ D.host.small := hk.1
  have hq : D.what₂.places.resChar w ≠ D.host.q := hk.2.1
  obtain ⟨M, hMnf, hM, hs⟩ := J.dgen
  obtain ⟨s, hsc, hsp⟩ := hs τ
  have h1 : ι (s : ℂ) = lamM M S.lam s := hι ⟨(s : ℂ), mem_Qbar M s⟩
  rw [t.O_dgen u μ, ← hsc, h1, lamM_apply]
  exact norm_generator_eq_one D _ S.lam h2 hq M hM τ s hsp
end

