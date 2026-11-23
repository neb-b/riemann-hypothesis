module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0007
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
public import Development.AutomorphicArithmetic.IdeleLatticeFacts.Bundle0002
public import Development.AutomorphicArithmetic.IdeleLatticeFacts.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.InertOfKept
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IdxSign
section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

private theorem sqrt_nat_pow (N k : ℕ) : Real.sqrt ((N ^ k : ℕ) : ℝ) = Real.sqrt (N : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), ih, pow_succ]

private theorem zpow_parity {s : Circle} (hs : s * s = 1) (a b : ℤ) (c : ℤ) (h : b = a + 2 * c) : s ^ b = s ^ a := by
  have h2 : s ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two, hs]
  rw [h, _root_.zpow_add, _root_.zpow_mul, h2, _root_.one_zpow, mul_one]

private theorem idx_split {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hIH : IdxHalf) (hcm : IsCMExt F E σ) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
    (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E} (hξ : σ ξ₀ = -ξ₀) {ψ : AddChar (AF F) ℂ}
    (hc : HeisClosedF σ JS JT ξ₀ ψ) {w : 𝓞 E} (hw : w + sgOF σ w = 1) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E))
    (hsd : ∀ p, SelfDual (gamFF σ JS JT ξ₀ ψ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)))
    (hfin : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0)
    {e : AEF F E} (he : IsSplitIdemF σ e) {g : GAF σ JS} {h : GAF σ JT} (hg : SuppAtF σ e JS g) (hh : SuppAtF σ e JT h) :
    idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) =
      idx ((latF F E nS nT Λ).map (mulFF e)) (((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))).map (mulFF e)) *
      idx (((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))).map (mulFF e)) ((latF F E nS nT Λ).map (mulFF e)) := by
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.FinLatSplitF.conj_conj_of_cm hcm
  have he' : IsSplitIdemF σ (cAF σ e) := GlobalTheory.FinLatSplitF.isSplitIdemF_conj he
  obtain ⟨hf, hfc, hcc⟩ := PositivityTheory.ThKW.LatB.split_parts he
  have heI : finPartF F E e ∈ PositivityTheory.ThKW.LatB.hatO (F := F) E :=
    GlobalTheory.AdIdem.mem_hat_of_idempotent F E _ (by rw [← map_mul, he.1])
  have hcI : finPartF F E (cAF σ e) ∈ PositivityTheory.ThKW.LatB.hatO (F := F) E :=
    GlobalTheory.AdIdem.mem_hat_of_idempotent F E _ (by rw [← map_mul, hcc])
  have hm : ∀ (a b : AEF F E) (x : XFF F E nS nT), mulFF a (mulFF b x) = (a * b) • x := fun a b x => smul_smul a b x
  have hSDA : SelfDual (gamFF σ JS JT ξ₀ ψ) (latF F E nS nT Λ) := by
    have := hsd 1
    rwa [map_one, Module.End.one_eq_id, Submodule.map_id] at this
  set ρ := rhoFF σ JS JT (g, h) with hρ
  have hρinj : Function.Injective ρ := by
    intro a b hab
    have h1 : ∀ c, rhoFF σ JS JT (g, h)⁻¹ (ρ c) = c := fun c => by
      rw [hρ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1 a, ← h1 b, hab]
  have hfix : ∀ x : XFF F E nS nT, ρ (x - mulFF e x - mulFF (cAF σ e) x) = x - mulFF e x - mulFF (cAF σ e) x := by
    intro x
    have hy : ((x - mulFF e x - mulFF (cAF σ e) x : XFF F E nS nT) : WOF F E nS nT) =
        (1 - (e + cAF σ e)) • (x : WOF F E nS nT) := by
      rw [XFF.coe_sub, XFF.coe_sub, coe_mulFF, coe_mulFF, sub_smul, add_smul, one_smul, sub_sub]
    refine XFF.ext ?_
    rw [coe_rhoFF, hy]
    show actOF σ JS JT g h ((1 - (e + cAF σ e)) • (x : WOF F E nS nT)) = _
    rw [actOF_smul]
    exact PositivityTheory.ThKW.LatB.act_supp hg hh _
  refine hIH (𝓞 E) (XFF F E nS nT) (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ) (sgOF σ) w (gamFF σ JS JT ξ₀ ψ) (opFF hc w)
    (isHeis_opFF hσ hS hT hξ hc hw) _ _ hSDA (hsd _) (hfin _) (mulFF e) (mulFF (cAF σ e))
    (fun x => by rw [hm, he.1]; rfl) (fun x => by rw [hm, he'.1]; rfl)
    (fun x => by rw [hm, he.2.1, zero_smul]) (fun x => by rw [hm, mul_comm, he.2.1, zero_smul])
    (fun x y => by rw [gamFF, gamFF, coe_mulFF, coe_mulFF, symplOF_smul σ JS JT hσ])
    (fun a ha => ⟨PositivityTheory.ThKW.LatB.int_smul_mem heI ha, PositivityTheory.ThKW.LatB.int_smul_mem hcI ha⟩)
    (fun a ha => ⟨PositivityTheory.ThKW.LatB.int_smul_mem_map _ heI ha, PositivityTheory.ThKW.LatB.int_smul_mem_map _ hcI ha⟩)
    (fun x => ⟨fun hx => ⟨_, hx, hfix x⟩, ?_⟩)
  rintro ⟨a, ha, hae⟩
  have : a = x - mulFF e x - mulFF (cAF σ e) x := hρinj (hae.trans (hfix x).symm)
  rwa [← this]

theorem UpperTheory.TP.W.idxSign :
    CardDet → IdxHalf → IdxSign := by
  intro _ hIH F E _ _ _ _ _ σ hcm nS nT JS JT hS hT ξ₀ hξ ψ hc w hw Λ hΛ hsd hfin lam hlam κ hκ e he g h hg hh x y hx hy
  obtain ⟨P, hPF, h1, h0⟩ := UpperTheory.exists_place_of_splitIdempotent_cmExt σ hcm e he
  have hinj := UpperTheory.eq_zero_of_splitIdempotent_eval_place_eq_zero σ hcm e he P h0
  obtain ⟨L, hfg, hsp, hL⟩ := UpperTheory.exists_local_lattice_of_global_lattice (F := F) P Λ hΛ
  have hone : ∀ {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : GAF σ J),
      (mtF σ J a).map (ev F E P) * (mtF σ J a⁻¹).map (ev F E P) = 1 := by
    intro n J a
    rw [← Matrix.map_mul, ← PositivityTheory.ThKW.LatB.mtF_mul, mul_inv_cancel, PositivityTheory.ThKW.LatB.mtF_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hone' : ∀ {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : GAF σ J),
      (mtF σ J a⁻¹).map (ev F E P) * (mtF σ J a).map (ev F E P) = 1 := by
    intro n J a
    have := hone J a⁻¹
    rwa [inv_inv] at this
  obtain ⟨T, hT1, hT2⟩ := UpperTheory.exists_linearMap_det_mul_mul_eq_pow ((mtF σ JT h).map (ev F E P)) ((mtF σ JS g⁻¹).map (ev F E P))
  have hTinj : Function.Injective T := by
    intro u v huv
    rw [hT1, hT1] at huv
    have h2 := congrArg (fun z => (mtF σ JT h⁻¹).map (ev F E P) * z * (mtF σ JS g).map (ev F E P)) huv
    have h3 : ∀ u : Matrix (Fin nT) (Fin nS) (P.adicCompletion E),
        (mtF σ JT h⁻¹).map (ev F E P) * ((mtF σ JT h).map (ev F E P) * u * (mtF σ JS g⁻¹).map (ev F E P)) *
          (mtF σ JS g).map (ev F E P) = u := by
      intro u
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hone' JS g, Matrix.mul_one, ← Matrix.mul_assoc, hone' JT h, Matrix.one_mul]
    rwa [h3, h3] at h2
  obtain ⟨e1, e2⟩ := UpperTheory.lattice_determinant_comparison_at_split_place σ JS JT e he.1 P h1 hinj Λ L hL g h T hT1
  obtain ⟨i, j, hi, hj, hv⟩ := UpperTheory.exists_lattice_index_of_injective_endomorphism P L T hfg hsp hTinj
  obtain ⟨s, hs1, hs2, hs3⟩ := UpperTheory.exists_sign_heckeChar_at_nonfixed_place σ lam κ hκ P hPF
  have hidx := idx_split σ hIH hcm hS hT hξ hc hw Λ hsd hfin he hg hh
  rw [e1, e2, hi, hj, ← pow_add] at hidx
  have hoff : ∀ (z : (AEF F E)ˣ) (d : AEF F E), (z : AEF F E) = e * d + (1 - e) → ∀ Q, Q ≠ P → wv F E Q z = 1 := by
    intro z d hz Q hQ
    rw [wv_apply, hz, map_add (f := _), map_mul, map_sub, map_one, h0 Q hQ, zero_mul, zero_add, sub_zero, map_one]
  have hat : ∀ (z : (AEF F E)ˣ) (d : AEF F E), (z : AEF F E) = e * d + (1 - e) → wv F E P z = Valued.v (ev F E P d) := by
    intro z d hz
    rw [wv_apply, hz, map_add (f := _), map_mul, map_sub, map_one, h1, one_mul, sub_self, add_zero]
  have hdet : ∀ {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : GAF σ J),
      ev F E P (mtF σ J a).det = ((mtF σ J a).map (ev F E P)).det := by
    intro n J a
    exact RingHom.map_det (ev F E P) (mtF σ J a)
  have hne : ∀ {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : GAF σ J), Valued.v ((mtF σ J a).map (ev F E P)).det ≠ 0 := by
    intro n J a
    have h2 := congrArg Matrix.det (hone J a)
    rw [Matrix.det_mul, Matrix.det_one] at h2
    exact (Valuation.ne_zero_iff _).2 (left_ne_zero_of_mul_eq_one h2)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v ((mtF σ JS g).map (ev F E P)).det = WithZero.exp m :=
    ⟨_, (WithZero.exp_log (hne JS g)).symm⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v ((mtF σ JT h).map (ev F E P)).det = WithZero.exp n :=
    ⟨_, (WithZero.exp_log (hne JT h)).symm⟩
  have hκx : κ x = s ^ m := hs3 x m (hoff x _ hx) (by rw [hat x _ hx, hdet, hm])
  have hκy : κ y = s ^ n := hs3 y n (hoff y _ hy) (by rw [hat y _ hy, hdet, hn])
  have hinv : Valued.v ((mtF σ JS g⁻¹).map (ev F E P)).det = WithZero.exp (-m) := by
    have h2 := congrArg (fun z => Valued.v (Matrix.det z)) (hone JS g)
    simp only [Matrix.det_mul, map_mul, Matrix.det_one, map_one, hm] at h2
    rw [WithZero.exp_neg]
    exact (inv_eq_of_mul_eq_one_right h2).symm
  have hrel : n * nS + -m * nT = (i : ℤ) - j := by
    rw [hT2, map_mul, map_pow, map_pow, hn, hinv, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add] at hv
    have := WithZero.exp_injective hv
    simpa [mul_comm] using this
  rw [hidx, map_pow, hs2, sqrt_nat_pow, mul_pow, hκx, hκy]
  have hz : (s ^ m) ^ nT * (s ^ n) ^ nS = s ^ ((i + j : ℕ) : ℤ) := by
    rw [← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, ← _root_.zpow_add]
    refine zpow_parity hs1 _ _ (m * nT - j) ?_
    push_cast
    linarith
  rw [hz, zpow_natCast]
  push_cast
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.LatK
section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA

theorem UpperTheory.TP.W.latK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E), GoodLat Λ → RatSD σ JS JT ξ₀ Λ →
      ∀ hc : HeisClosedF σ JS JT ξ₀ B.ψ, ∃ (w : 𝓞 E) (lam : ℕ →* ℂ)
        (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ Λ hg hsd hc
  have hσ := LatB.sg_sg hB.cm
  obtain ⟨w, hw⟩ := LatB.exists_w hB.cm hB.unram
  obtain ⟨lam, hlam⟩ := UpperTheory.TP.W.normK F E σ B hB
  have H := isHeis_opFF hσ hS hT hξ hc hw
  have hA := LatC.lat_sd hσ hB.std hg hsd
  have hspan := _root_.GlobalTheory.FinWeil.span_translates_vacua H _ hA (LatC.smooth_theta hg H hA)
  have hidx : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0 := fun p => by
    refine LatC.idx_ne_zero hg _ (AddMonoidHom.mk' (actOF σ JS JT p.1 p.2) (GlobalTheory.FinLatF.actOF_add _ _))
      (LatC.continuous_act_right p.1 p.2) (fun l hl => actOF_mem_finSubF _ _ (lat_fin hl)) ?_
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  obtain ⟨Om, h1, h2⟩ := _root_.GlobalTheory.FinWeil.exists_weil_rep_of_vacua H lam hlam _ hA hspan (rhoFF σ JS JT) (LatA.gamFF_rhoFF hS) hidx
  refine ⟨w, lam, Om, hw, hA, hspan, hidx, h1, fun p => (h2 p).1, fun p => (h2 p).2, hlam, fun x => ?_,
    LatC.near hg, LatC.near' hg, fun e he a ha => ?_⟩
  · obtain ⟨M, hM, hx⟩ := lat_den hg (x : WOF F E nS nT) x.fin
    refine ⟨2 * M, by omega, fun l hl => ?_⟩
    have h3 : gamFF σ JS JT ξ₀ B.ψ x (M • l) = 1 := by
      rw [H.nsmul_right, ← H.nsmul_left]
      exact H.iso hA hx hl
    rw [mul_smul, LatC.symplOHF_two]
    exact h3
  · obtain ⟨hf, hfc, hcc⟩ := LatB.split_parts he
    exact ⟨LatB.idem_smul_mem he.1 hf ha, LatB.idem_smul_mem hcc hfc ha⟩

end
end

