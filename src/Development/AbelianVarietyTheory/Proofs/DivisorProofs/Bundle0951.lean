module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryOsc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0911
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0196
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPlaceDatumOverNumberField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevelDatum

variable {D : D7}

def rowP (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (x : Fin W.rank → D.host.E) (a : Fin W.rank) : EAf D :=
  toEAf D e * ∑ k, eToEAf D (∑ l, D.sp.cm.sig (x l) * W.gram l k) * β.val k a

theorem rowPairing_add (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (x y : Fin W.rank → D.host.E) (a : Fin W.rank) :
    rowP W β e (x + y) a = rowP W β e x a + rowP W β e y a := by
  simp only [rowP, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib, mul_add]

theorem rowPairing_zero (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (a : Fin W.rank) :
    rowP W β e 0 a = 0 := by
  simp only [rowP, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, mul_zero]

theorem rowPairing_smul (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (c : D.host.E) (x : Fin W.rank → D.host.E)
    (a : Fin W.rank) : rowP W β e (c • x) a = eToEAf D (D.sp.cm.sig c) * rowP W β e x a := by
  simp only [rowP, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum]
  ring

theorem uMat_eq (V W : HSp D) (hV : V.gram = 1) (βV : GL (Fin V.rank) (EAf D)) (β : GL (Fin W.rank) (EAf D)) (e : AE D)
    (X : Fin V.rank → Fin W.rank → D.host.E) (b : Fin V.rank) (a : Fin W.rank) :
    FWT.uMat V W βV β e X b a = ∑ b', (βV⁻¹).val b b' * rowP W β e (X b') a := by
  simp only [FWT.uMat, rowP, hV, inv_one, Matrix.one_mul, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem eToEAf_int (c : 𝓞 D.host.E) : eToEAf D (c : D.host.E) = (oToS D.host.F D.host.E c : Formalism.L2.Herm.intAf D.host.F D.host.E) := rfl

theorem exists_sig (c : 𝓞 D.host.E) : ∃ c' : 𝓞 D.host.E, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E) :=
  ⟨⟨_, (RingOfIntegers.isIntegral_coe c).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom⟩, rfl⟩

theorem rowP_int (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E))
    (hβ : IsSDFrame W β Λ 1) (e : AE D) (P : Finset (Pl D.host.E)) (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (x : Fin W.rank → D.host.E) (hx : x ∈ latG W 1) (a : Fin W.rank) :
    rowP W β e x a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [rowPairing_smul, rowP, ← mul_assoc, mul_comm _ (toEAf D e)]
    exact mul_mem (GlobalTheory.IdemIntegral.conj_mem_intAf D e P he hP c hc) (GlobalTheory.PairIntegral.pair_mem_intAf D W β Λ hβ v hv a)
  | zero => rw [rowPairing_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [rowPairing_add]; exact add_mem hx hy
  | smul c x _ hx =>
    obtain ⟨c', hc'⟩ := exists_sig c
    rw [show c • x = (c : D.host.E) • x from rfl, rowPairing_smul, ← hc', eToEAf_int]
    exact mul_mem (Subtype.prop _) hx

theorem residue_rowPairing_eq_zero (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (a : Fin W.rank)
    (hi : ∀ x, rowP W β e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (J : Ideal (𝓞 D.host.E)) (PP : Pl D.host.E)
    (hJ : ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E))
    (x : La) (hx : x ∈ J • (⊤ : Submodule (𝓞 D.host.E) La)) : resS D.host.F PP ⟨_, hi x⟩ = 0 := by
  refine Submodule.smul_induction_on (p := fun x => resS D.host.F PP ⟨_, hi x⟩ = 0) hx (fun c hc y _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨c', hc', e'⟩ := hJ c hc
    have : (⟨_, hi (c • y)⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = oToS D.host.F D.host.E c' * ⟨_, hi y⟩ := by
      refine Subtype.ext ?_
      change rowP W β e (ι (c • y)) a = eToEAf D (c' : D.host.E) * rowP W β e (ι y) a
      rw [map_smul, show c • ι y = (c : D.host.E) • ι y from rfl, rowPairing_smul, e']
    rw [this, map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hc', zero_mul]
  · have : (⟨_, hi (x + y)⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi x⟩ + ⟨_, hi y⟩ := by
      refine Subtype.ext ?_
      change rowP W β e (ι (x + y)) a = rowP W β e (ι x) a + rowP W β e (ι y) a
      rw [map_add (f := _), rowPairing_add]
    rw [this, RingHom.map_add, hx, hy, add_zero]

theorem redM_uMat (V W : HSp D) (hV : V.gram = 1) (βV : GL (Fin V.rank) (EAf D)) (hβ : IsIntM (βV⁻¹).val)
    (β : GL (Fin W.rank) (EAf D)) (e : AE D) (X : Fin V.rank → Fin W.rank → D.host.E)
    (hi : ∀ b a, rowP W β e (X b) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    IsIntM (FWT.uMat V W βV β e X) ∧ ∀ PP b a, redM PP (FWT.uMat V W βV β e X) b a =
      ∑ b', resS D.host.F PP ⟨_, hβ b b'⟩ * resS D.host.F PP ⟨_, hi b' a⟩ := by
  have h : IsIntM (FWT.uMat V W βV β e X) := fun b a => by
    rw [uMat_eq V W hV]
    exact sum_mem fun b' _ => mul_mem (hβ b b') (hi b' a)
  refine ⟨h, fun PP b a => ?_⟩
  rw [redM, dite_eq_left (h b a)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_mul, ← map_sum]
  congr 1
  refine Subtype.ext ?_
  rw [AddSubmonoidClass.coe_finsetSum]
  exact uMat_eq V W hV βV β e X b a

theorem omega_congr {a b : ℕ} (Pg Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (h : ∀ PP, PP ∈ Pg ∨ PP ∈ Q → y PP = y' PP) :
    omegaK Pg y * omegaQ Q r ξ k y = omegaK Pg y' * omegaQ Q r ξ k y' := by
  classical
  have h1 : omegaK Pg y = omegaK Pg y' := by
    unfold omegaK
    refine if_congr (forall₂_congr fun PP hPP => by rw [h PP (Or.inl hPP)]) rfl rfl
  have h2 : omegaQ Q r ξ k y = omegaQ Q r ξ k y' := by
    have e : (∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det) ↔
        ∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det :=
      forall₂_congr fun PP hPP => by rw [h PP (Or.inr hPP)]
    unfold omegaQ
    by_cases c : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
    · rw [dite_eq_left c, dite_eq_left (e.1 c)]
      refine Finset.prod_congr rfl fun PP _ => ?_
      have : (c PP.1 PP.2).2.unit = (e.1 c PP.1 PP.2).2.unit := Units.ext (by
        rw [IsUnit.unit_spec, IsUnit.unit_spec, h PP.1 (Or.inr PP.2)])
      rw [this]
    · rw [dite_eq_right c, dite_eq_right (fun c' => c (e.2 c'))]
  rw [h1, h2]

theorem exists_omega_field (Pg Q : Finset (Pl D.host.E)) : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
    ∀ {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
      (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)), omegaK Pg y * omegaQ Q r ξ k y ∈ M := by
  have hf : ∀ PP : Pl D.host.E, 0 < Nat.card (kP PP)ˣ := fun PP => by
    have : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
    exact Nat.card_pos
  obtain ⟨M, hM, h⟩ := GlobalTheory.Mem.FrameVal.exists_roots (∏ PP ∈ Q, Nat.card (kP PP)ˣ) (Finset.prod_pos fun PP _ => hf PP)
  refine ⟨M, hM, fun r ξ k y => mul_mem ?_ ?_⟩
  · unfold omegaK
    split_ifs
    exacts [one_mem _, zero_mem _]
  · unfold omegaQ
    split_ifs
    · refine prod_mem fun PP _ => zpow_mem (h _ ?_) _
      obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem (fun PP : Pl D.host.E => Nat.card (kP PP)ˣ) PP.2
      rw [hu, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one, one_pow]
    · exact zero_mem _


set_option maxHeartbeats 800000 in
theorem exists_datum (V W : HSp D) (hV : V.gram = 1) (βV : GL (Fin V.rank) (EAf D)) (hβ : IsIntM (βV⁻¹).val)
    (β : GL (Fin W.rank) (EAf D)) (e : AE D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E))
    (hi : ∀ x a, rowP W β e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (J : Ideal (𝓞 D.host.E)) (PP : Pl D.host.E)
    (hJ : ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E))
    (x z : Fin V.rank → La) (h : ∀ b, z b - x b ∈ J • (⊤ : Submodule (𝓞 D.host.E) La)) :
    redM PP (FWT.uMat V W βV β e fun b => ι (z b)) = redM PP (FWT.uMat V W βV β e fun b => ι (x b)) := by
  have key : ∀ b' a, resS D.host.F PP ⟨_, hi (z b') a⟩ = resS D.host.F PP ⟨_, hi (x b') a⟩ := fun b' a => by
    have h2 := residue_rowPairing_eq_zero W β e ι a (fun x => hi x a) J PP hJ _ (h b')
    have : (⟨_, hi (z b') a⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi (z b' - x b') a⟩ + ⟨_, hi (x b') a⟩ := by
      refine Subtype.ext ?_
      change rowP W β e (ι (z b')) a = rowP W β e (ι (z b' - x b')) a + rowP W β e (ι (x b')) a
      rw [← rowPairing_add, ← LinearMap.map_add (f := _), sub_add_cancel]
    rw [this, RingHom.map_add (f := _), h2, zero_add]
  funext b a
  exact ((redM_uMat V W hV βV hβ β e (fun b => ι (z b)) fun b a => hi (z b) a).2 PP b a).trans
    ((Finset.sum_congr rfl fun b' _ => congrArg _ (key b' a)).trans
      ((redM_uMat V W hV βV hβ β e (fun b => ι (x b)) fun b a => hi (x b) a).2 PP b a).symm)


set_option maxHeartbeats 1000000 in
theorem exists_phi : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_vP → ∀ (i : Fin D.R.m), VStd D i → ∀ (t : T0) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ M' : IntermediateField ℚ ℂ, M ≤ M' → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ J : Ideal (𝓞 D.host.E), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E)) → ∃ φ : (Fin (Vc D i).rank → La ⧸ (J • ⊤ : Submodule (𝓞 D.host.E) La)) → M', PhiIs R i M'.val.toRingHom t ι (J • ⊤) φ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hlev hvP i hV t La _ _ ι hι
  obtain ⟨M, hM, hv⟩ := exists_omega_field R.Pg (R.Q t)
  refine ⟨M, hM, fun M' hle hP J hJ => ?_⟩
  obtain ⟨-, e, he, -⟩ := hvP i t
  have hβ := GlobalTheory.StdFrameInv.isIntM_inv D i _ _ hV (hlev.βV i)
  have hi : ∀ x a, rowP (Wc D i) (R.βW i) e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun x a =>
    rowP_int _ _ _ (hlev.βW i) e _ he (fun PP h => hP PP (by simpa using h)) _
      (hι.2.le (LinearMap.mem_range_self ι x)) a
  refine ⟨fun q => ⟨_, hle (hv (Wc D i).rank (R.xiR t) (-1) fun PP => redM PP
    (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (q b).out))⟩, e, he, fun x =>
    ⟨(redM_uMat (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e (fun b => ι (x b)) fun b a => hi (x b) a).1, ?_⟩⟩
  exact omega_congr _ _ _ _ _ _ _ fun PP hPP => exists_datum (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e ι hi J PP (hJ PP hPP) x _
    fun b => (Submodule.Quotient.eq _).1 (Quotient.out_eq _)

end GlobalTheory.LevelDatum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionNormalisingSchrodingerOper
section
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil Matrix

noncomputable section

namespace GlobalTheory.SchrodOsc

section Sign

variable {N : Type} [Fintype N] [DecidableEq N] (pos : N → Bool)

def signEquiv : N ≃ Fin (Fintype.card {n // pos n = true}) ⊕ Fin (Fintype.card {n // ¬ pos n = true}) :=
  (Equiv.sumCompl (fun n => pos n = true)).symm.trans
    (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _))

theorem pos_signEquiv_symm_inl (i : Fin (Fintype.card {n // pos n = true})) :
    pos ((signEquiv pos).symm (Sum.inl i)) = true := by
  simp only [signEquiv, Equiv.symm_trans_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.symm_symm, Equiv.sumCompl_apply_inl]
  exact ((Fintype.equivFin _).symm i).2

theorem pos_signEquiv_symm_inr (j : Fin (Fintype.card {n // ¬ pos n = true})) :
    pos ((signEquiv pos).symm (Sum.inr j)) = false := by
  simp only [signEquiv, Equiv.symm_trans_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.symm_symm, Equiv.sumCompl_apply_inr]
  simpa using ((Fintype.equivFin _).symm j).2

theorem fromBlocks_eq_reindex :
    (fromBlocks 1 0 0 (-1) : Matrix (Fin (Fintype.card {n // pos n = true}) ⊕ Fin (Fintype.card {n // ¬ pos n = true}))
      (Fin (Fintype.card {n // pos n = true}) ⊕ Fin (Fintype.card {n // ¬ pos n = true})) ℂ) =
      reindex (signEquiv pos) (signEquiv pos) (diagonal fun n => if pos n then 1 else -1) := by
  rw [reindex_apply, submatrix_diagonal_equiv]
  have h1 : (1 : Matrix (Fin (Fintype.card {n // pos n = true})) (Fin (Fintype.card {n // pos n = true})) ℂ) =
      diagonal fun _ => 1 := diagonal_one.symm
  have h2 : (-1 : Matrix (Fin (Fintype.card {n // ¬ pos n = true})) (Fin (Fintype.card {n // ¬ pos n = true})) ℂ) =
      diagonal fun _ => -1 := by rw [← diagonal_neg, diagonal_one]
  rw [h1, h2, fromBlocks_diagonal]
  congr 1
  funext i
  rcases i with i | j
  · simp [pos_signEquiv_symm_inl]
  · simp [pos_signEquiv_symm_inr]

end Sign

end GlobalTheory.SchrodOsc

namespace GlobalTheory.SchrodOsc

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ}

def sgn (n : Ix R S × (ι × Ix P Q)) : Bool := linePos (p := P) (q := Q) (r := R) (s := S) (n.2.2, n.1)

theorem lineSign_eq (a : Ix P Q) (b : Ix R S) : lineSign a b = if linePos (a, b) then 1 else -1 := by
  rcases a with a | a <;> rcases b with b | b <;> rfl

theorem Jm_transpose (R S : ℕ) : (Jm R S)ᵀ = Jm R S := by
  simp [Jm, Formalism.UG.Jpq, fromBlocks_transpose]

theorem diagonal_sgn : (diagonal fun n : Ix R S × (ι × Ix P Q) => if sgn n then (1 : ℂ) else -1) =
    blockDiagonal fun o : ι × Ix P Q => Jm P Q o.2 o.2 • Jm R S := by
  ext ⟨b, w, a⟩ ⟨b', w', a'⟩
  rcases a with a | a <;> rcases b with b | b <;> rcases b' with b' | b' <;>
    simp [diagonal_apply, blockDiagonal_apply, Jm, Formalism.UG.Jpq, sgn, linePos, one_apply, Prod.ext_iff] <;>
    split_ifs <;> simp_all [Matrix.one_apply]

theorem blockDiagonal_mem (M : ι → Mat R S) (hM : ∀ w, (M w)ᴴ * Jm R S * M w = Jm R S) :
    (blockDiagonal fun o : ι × Ix P Q => M o.1)ᵀ *
        (diagonal fun n : Ix R S × (ι × Ix P Q) => if sgn n then (1 : ℂ) else -1) *
        (blockDiagonal fun o : ι × Ix P Q => M o.1).map star =
      diagonal fun n : Ix R S × (ι × Ix P Q) => if sgn n then (1 : ℂ) else -1 := by
  rw [diagonal_sgn, blockDiagonal_transpose, blockDiagonal_map _ _ (star_zero ℂ), ← blockDiagonal_mul,
    ← blockDiagonal_mul]
  congr 1
  funext o
  have h := congrArg transpose (hM o.1)
  rw [transpose_mul, transpose_mul, Jm_transpose] at h
  have e : (M o.1)ᴴᵀ = (M o.1).map star := by ext; simp
  rw [e] at h
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h]

end Block

end GlobalTheory.SchrodOsc

namespace GlobalTheory.SchrodOsc

section Hom

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} {G : Type} [Group G]

abbrev lineNum (ι : Type) [Fintype ι] [DecidableEq ι] (P Q R S : ℕ) :=
  signEquiv (sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S))

def blockHom (P Q : ℕ) (k : G →* (ι → Mat R S)) :
    G →* Matrix (Ix R S × (ι × Ix P Q)) (Ix R S × (ι × Ix P Q)) ℂ where
  toFun g := blockDiagonal fun o : ι × Ix P Q => k g o.1
  map_one' := by
    simp only [map_one, Pi.one_apply]
    exact blockDiagonal_one
  map_mul' g g' := by simp [blockDiagonal_mul]

def numHom (P Q : ℕ) (k : G →* (ι → Mat R S)) : G →* Matrix (Fin (Fintype.card {n // sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕ Fin (Fintype.card {n // ¬ sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}))
      (Fin (Fintype.card {n // sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕ Fin (Fintype.card {n // ¬ sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true})) ℂ :=
  (reindexAlgEquiv ℂ ℂ (lineNum ι P Q R S)).toAlgHom.toRingHom.toMonoidHom.comp (blockHom P Q k)

theorem numHom_apply (k : G →* (ι → Mat R S)) (g : G) :
    numHom P Q k g = reindex (lineNum ι P Q R S) (lineNum ι P Q R S) (blockDiagonal fun o : ι × Ix P Q => k g o.1) :=
  rfl

theorem numHom_mem (k : G →* (ι → Mat R S)) (hk : ∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) (g : G) :
    (numHom P Q k).toHomUnits g ∈ GlobalTheory.WeilM.UG (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) (fromBlocks 1 0 0 (-1)) := by
  have hc : ⇑(Complex.conjAe : ℂ →ₐ[ℝ] ℂ) = star := funext fun x => by simp
  show (numHom P Q k g)ᵀ * fromBlocks 1 0 0 (-1) * (numHom P Q k g).map (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) =
    fromBlocks 1 0 0 (-1)
  rw [hc, numHom_apply, fromBlocks_eq_reindex, transpose_reindex]
  have hm : (reindex (lineNum ι P Q R S) (lineNum ι P Q R S) (blockDiagonal fun o : ι × Ix P Q => k g o.1)).map star =
      reindex (lineNum ι P Q R S) (lineNum ι P Q R S) ((blockDiagonal fun o : ι × Ix P Q => k g o.1).map star) := rfl
  rw [hm, ← reindexAlgEquiv_apply ℂ ℂ, ← reindexAlgEquiv_apply ℂ ℂ, ← reindexAlgEquiv_apply ℂ ℂ, ← map_mul, ← map_mul,
    blockDiagonal_mem _ (hk g)]

def unitHom (P Q : ℕ) (k : G →* (ι → Mat R S)) (hk : ∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) :=
  (numHom P Q k).toHomUnits.codRestrict _ (numHom_mem k hk)

theorem continuous_unitHom [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (ι → Mat R S)) (hc : Continuous k)
    (hk : ∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) : Continuous (unitHom P Q k hk) := by
  have hn : Continuous (numHom P Q k) := by
    show Continuous fun g => reindex (lineNum ι P Q R S) (lineNum ι P Q R S) (blockDiagonal fun o : ι × Ix P Q => k g o.1)
    exact (Continuous.matrix_blockDiagonal (continuous_pi fun (o : ι × Ix P Q) => (continuous_apply o.1).comp hc)).matrix_reindex _ _
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hn, ?_⟩)
  have : (fun g => (((Subtype.val ∘ unitHom P Q k hk) g)⁻¹ : GL _ ℂ).val) = fun g => numHom P Q k g⁻¹ := by
    funext g
    simp only [Function.comp_apply]
    rw [← Subgroup.coe_inv, ← map_inv]
    rfl
  rw [this]
  exact hn.comp continuous_inv

end Hom

end GlobalTheory.SchrodOsc

namespace GlobalTheory.SchrodOsc

section Final

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ}

def coordOf (z : Fin (Fintype.card {n // sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕
    Fin (Fintype.card {n // ¬ sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) → ℂ) :
    ι → Matrix (Ix P Q) (Ix R S) ℂ :=
  fun w a b => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * z (lineNum ι P Q R S (b, (w, a)))

theorem coordOf_add (z z' : Fin (Fintype.card {n // sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕
    Fin (Fintype.card {n // ¬ sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) → ℂ) :
    coordOf (z + z') = coordOf z + coordOf z' := by
  funext w a b
  simp [coordOf, mul_add]

theorem continuous_coordOf : Continuous (coordOf (ι := ι) (P := P) (Q := Q) (R := R) (S := S)) :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_pi fun _ => continuous_const.mul (continuous_apply _)

theorem two_mul_sum_coordOf (z z' : Fin (Fintype.card {n // sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕
    Fin (Fintype.card {n // ¬ sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) → ℂ) :
    2 * ∑ w, ∑ a, ∑ b, lineSign a b * coordOf z w a b * star (coordOf z' w a b) =
      (∑ i, z (Sum.inl i) * star (z' (Sum.inl i))) - ∑ j, z (Sum.inr j) * star (z' (Sum.inr j)) := by
  set e := lineNum ι P Q R S with he
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 2⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    push_cast
    rfl
  let F : Ix R S × (ι × Ix P Q) → ℂ := fun n => (if sgn n then 1 else -1) * z (e n) * star (z' (e n))
  have h1 : ∀ w a b, lineSign a b * coordOf z w a b * star (coordOf z' w a b) = 2⁻¹ * F (b, (w, a)) := by
    intro w a b
    simp only [coordOf, F, star_mul, sgn, lineSign_eq]
    rw [← hs, he]
    by_cases h : linePos (a, b) = true <;> simp only [h, ↓reduceIte, Bool.false_eq_true] <;> ring
  have h2 : ∑ n, F n = ∑ w, ∑ a, ∑ b, F (b, (w, a)) := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ => Finset.sum_comm
  have h3 : ∑ n, F n = ∑ i, F (e.symm i) := (e.symm.sum_comp F).symm
  simp_rw [h1, ← Finset.mul_sum, ← h2, h3, Fintype.sum_sum_type]
  simp only [F, he, pos_signEquiv_symm_inl, pos_signEquiv_symm_inr, Equiv.apply_symm_apply]
  simp
  ring

theorem coordOf_mulVec {G : Type} [Group G] (k : G →* (ι → Mat R S)) (hk : ∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S)
    (g : G) (z : Fin (Fintype.card {n // sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕
    Fin (Fintype.card {n // ¬ sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) → ℂ) :
    coordOf (((unitHom P Q k hk g).1 : Matrix _ _ ℂ) *ᵥ z) = fun w => coordOf z w * (k g w)ᵀ := by
  show coordOf (numHom P Q k g *ᵥ z) = _
  rw [numHom_apply, reindex_apply, submatrix_mulVec_equiv]
  funext w
  ext a b
  simp only [Matrix.mul_apply, transpose_apply, coordOf]
  simp [mulVec, dotProduct, blockDiagonal_apply, Fintype.sum_prod_type, ite_mul]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring

end Final

end GlobalTheory.SchrodOsc

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

theorem GlobalTheory.SchrodOsc.exists_osc : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    (∀ v : L2 l, Continuous fun w : l ⊕ l → ℝ => rho w v) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (ι → Mat R S)), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) →
    ∃ ω : G →* (L2 l ≃ₗᵢ[ℂ] L2 l), (∀ v, Continuous fun g => ω g v) ∧
      ∀ g c v, ω g (rho (φ c) v) = rho (φ fun w => c w * (k g w)ᵀ) (ω g v) := by
  intro ι l _ _ _ _ P Q R S φ hφ hcont G _ _ _ k hkc hk
  obtain ⟨ω₀, hω₀c, hω₀, -⟩ := GlobalTheory.FockRep.exists_unitary_osc _ _ (L2 l)
    (fun z => rho (φ (GlobalTheory.SchrodOsc.coordOf z)))
    (fun v => (hcont v).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      GlobalTheory.SchrodOsc.continuous_coordOf))
    (fun z z' v => by
      rw [rho_rho, ← map_add (f := _), ← GlobalTheory.SchrodOsc.coordOf_add, hφ, ← GlobalTheory.SchrodOsc.two_mul_sum_coordOf]
      congr 2
      simp [Complex.mul_im]
      ring)
  refine ⟨ω₀.comp (GlobalTheory.SchrodOsc.unitHom P Q k hk), fun v => (hω₀c v).comp (GlobalTheory.SchrodOsc.continuous_unitHom k hkc hk),
    fun g c v => ?_⟩
  obtain ⟨z, hz⟩ : ∃ z, GlobalTheory.SchrodOsc.coordOf (ι := ι) (P := P) (Q := Q) (R := R) (S := S) z = c := by
    refine ⟨fun i => ((Real.sqrt 2 : ℝ) : ℂ) * (fun n : Ix R S × (ι × Ix P Q) => c n.2.1 n.2.2 n.1)
      ((GlobalTheory.SchrodOsc.lineNum ι P Q R S).symm i), ?_⟩
    funext w a b
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
    simp [GlobalTheory.SchrodOsc.coordOf, h2]
  have h := hω₀ (GlobalTheory.SchrodOsc.unitHom P Q k hk g) z v
  rw [hz, GlobalTheory.SchrodOsc.coordOf_mulVec, hz] at h
  exact h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulRatEqIntOfIntegralAwayStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_pow_mul_rat_eq_int_of_integral_away : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), (∀ v : AwayP p, algebraMap ℚ (v.1.adicCompletion ℚ) q ∈ v.1.adicCompletionIntegers ℚ) → ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * q = z := by
  first | (exact @GlobalTheory.ratint_away) | (exact GlobalTheory.ratint_away) | (intros; apply GlobalTheory.ratint_away  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeSaturationGenericHyperplaneSectionStatement
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_saturation_generic_hyperplane_section : ∀ (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K)), P.IsPrime → (∀ u : Fin N → AlgebraicClosure K, ∃ y : Fin N → AlgebraicClosure K, y ≠ 0 ∧ (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, u j * y j = 0) → ∃ Q : Ideal (MvPolynomial (Fin N) L), Q.IsPrime ∧ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔ Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L)} ≤ Q ∧ ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔ Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L)} := by
  first | exact @GlobalTheory.Chow.exists_prime_saturation_generic_section | exact GlobalTheory.Chow.exists_prime_saturation_generic_section | (intros; apply GlobalTheory.Chow.exists_prime_saturation_generic_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPointPolynomialIdempotentUnitValueStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalPoint_polynomial_idempotentUnit_value : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F))) (ψ : Polynomial (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), (∀ (Ω : Type) [Field Ω] (φ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Ω), φ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LocalGlobalChar.eps S)) = 1 → ψ.map φ ≠ 0) → ∃ t : F, IsUnit (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LocalGlobalChar.eps S) * ψ.eval (algebraMap F (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) t) + (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LocalGlobalChar.eps S))) := by
  first | exact @GlobalTheory.DenseAvoid.exists_unit_eval | exact GlobalTheory.DenseAvoid.exists_unit_eval | (intros; apply GlobalTheory.DenseAvoid.exists_unit_eval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroChartOfEffectiveClassStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_nonzero_chart_of_effective_class : ∀ {X : Scheme.{0}} (N : LB X) (hN : N.IsLB), GlobalTheory.EffBound.Eff (GlobalTheory.CechPic.cls N hN) → ∃ (σ : LB.Sec N) (j : N.ι), σ.f j ≠ 0 := by
  first | exact @GlobalTheory.EffBound.exists_sec_of_eff | exact GlobalTheory.EffBound.exists_sec_of_eff | (intros; apply GlobalTheory.EffBound.exists_sec_of_eff <;> assumption)
end

