module

public import Formalism.LocalToGlobal.Columns.XiTopTilRefHolds
public import Formalism.LocalToGlobal.Columns.Bundle0047
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.HilbertNinetyNormOne

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.ChainTopTilQ
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem tq_tfaZ_symm {N n : ℕ} (hN : N = n + 1) (f : Sp E n ≃ₗ[E] Sp E n) (z : E) (hz : z ≠ 0) (v : Sp E N) (i : Fin N) :
    (Sc.Fr.tfaExtZ hN f z hz).symm v i =
      if h : i.1 < n then f.symm (fun j : Fin n => v ⟨j.1, by omega⟩) ⟨i.1, h⟩ else z⁻¹ * v i := by
  subst hN
  show (Sc.Fr.tfaD z hz).symm ((extE f).symm v) i = _
  rw [Sc.Fr.tfaD_symm_apply]
  by_cases h : i.1 < n
  · rw [dif_pos h, if_neg (fun h' => by rw [h'] at h; simp at h)]
    obtain ⟨j, rfl⟩ : ∃ j : Fin n, i = Fin.castSucc j := ⟨⟨i.1, h⟩, Fin.ext rfl⟩
    show initL E n ((extE f).symm v) j = _
    rw [initL_extE_symm]
    rfl
  · rw [dite_eq_right h]
    obtain rfl : i = Fin.last n := Fin.ext (by have := i.2; simp; omega)
    rw [if_pos rfl, extE_symm_last]

end Gen

section Fin

variable {X : Fields} {Pr : Primes X} {R : Ranks}
variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))


open Classical in
set_option maxHeartbeats 1600000 in
theorem xiTopTilQ_holds (hX : X.Ok) (hPr : Pr.Ok) (hc : cst.Ok) {m2 : ℕ} (hm : R.m = m2 + 2) (u : Pr.Word)
    (hpi : ∀ w : rowSG Pr sel mu, Pr.piT u ∉ w.1.asIdeal)
    (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (d : RowPt Pr R sel mu)
    (p' : DecoF X.E (R.N R.m) (Pr.vT u) Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (hp' : p'.deco = tilC sel mu u d)
    (hfr : ∀ (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)),
      p'.fr ⟨P, hP⟩ = (Sc.Fr.topFrA (R := R) sel mu u (Finset.subset_union_left : Pr.vGs ⊆ rowSG Pr sel mu)
        (fun P hP => Finset.mem_union_right _ hP)).fr ⟨P, hP⟩ d)
    (hY : Y ∈ ybSet sel mu cst p.deco.1.N) :
    XiTopG Ch sel mu cst (m2 + 1) R.m (R.N R.m) p Y p' = XiCpl2 Ch sel mu cst m2 p Y d := by
  classical
  funext x
  unfold XiTopG XiCpl2
  have e0 : phiT X.K p.deco.1 p'.deco.1 x = phiT X.K p.deco.1 (tilQ sel mu u d).1 x := by rw [hp']; rfl
  rw [e0]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  have hlast : R.N R.m - 1 < R.N R.m := by have := R.N_pos R.m; omega
  by_cases hP : P.1 ∈ Pr.vGs
  · have eF : frsG sel mu p' P = (tilQ sel mu u d).1.liftFr P := by
      unfold frsG
      rw [dif_pos hP, hp']
      rfl
    have ef : frsF sel mu p P = p.deco.1.liftFr ⟨P.1, hP⟩ := by
      unfold frsF
      rw [dif_pos hP]
    rw [eF]
    have hT : ∀ Q : Pr.vT u, cO X.E (Pr.piT u) ∉ Q.1.asIdeal := fun Q => conj_piT_notMem hPr u Q
    have hG : ∀ w : rowSG Pr sel mu, Pr.piT u ∉ w.1.asIdeal := hpi
    have hF' : (DecoSet.tilH (ST := Pr.vT u) (N_m_succ R) (Pr.piT u) d).1.IsLift P ((tilQ sel mu u d).1.liftFr P) :=
      Deco.liftFr_spec ((tilQ sel mu u d).2.hasLift P)
    have hf0 : d.1.IsLift P (d.1.liftFr P) := Deco.liftFr_spec (d.2.hasLift P)
    have key := xtLocal (K := X.K) (P := P.1) (q := qOf P.1) (ciQ_mem P.1) (ciQ_notMem_sq hX hPr hP) (k₀ := R.k) (c' := cOf R (m2 + 1))
      (n' := R.N (m2 + 1)) (n := R.N R.m - 1) (N := R.N R.m) (xt_cOf hm) (PhiTop Ch mu cst.sharp m2 P.1)
      (fun x x' h => xtPhiTop_congr Ch mu hX hPr hm cst.sharp hP x x' h) (fun x h => xtPhiTop_int Ch mu hm cst.sharp hP x h)
      (cst.psi P) (cst.D P) (hc.D_pos P) (hc.psi_add P) (hc.psi_int P) epsSg (prXp X.E R) (atNL X.E (R.N R.m) (R.N R.m - 1))
      (fun a => by
        constructor
        · intro h
          refine ⟨fun i => h _, ?_⟩
          unfold atNL
          rw [dif_pos hlast]
          exact h _
        · rintro ⟨h1, h2⟩ i
          by_cases hi : i.1 < R.N R.m - 1
          · exact h1 ⟨i.1, by omega⟩
          · unfold atNL at h2
            rw [dif_pos hlast] at h2
            have : i = ⟨R.N R.m - 1, hlast⟩ := Fin.ext (by show i.1 = R.N R.m - 1; have := i.2; omega)
            rw [this]
            exact h2)
      (((tilQ sel mu u d).1.liftFr P).symm.toLinearMap ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap)
      ((d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap)
      ((((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap)
      (fun j => by
        have h := xtMid (ST := Pr.vT u) (N_m_succ R) d hT hG P _ hF' _ hf0 (x (frsF sel mu p P (Pi.single j 1)))
        have el : ∀ a : Sp X.E (R.N R.m), atNL X.E (R.N R.m) (R.N R.m - 1) a = a ⟨R.N R.m - 1, hlast⟩ := fun a => by
          unfold atNL
          rw [dif_pos hlast]
          rfl
        refine ⟨?_, fun hall => ⟨fun i => ?_, ?_⟩⟩
        · refine h.1.trans (and_congr Iff.rfl ?_)
          show _ ↔ IntAt P.1 (((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ * atNL X.E (R.N R.m) (R.N R.m - 1) (x (frsF sel mu p P (Pi.single j 1))))
          rw [el]
        · exact (h.2 hall).1 ⟨i.1, by have := i.2; omega⟩
        · show redP P.1 (atNL X.E (R.N R.m) (R.N R.m - 1) _) =
            redP P.1 (((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ * atNL X.E (R.N R.m) (R.N R.m - 1) (x (frsF sel mu p P (Pi.single j 1))))
          rw [el, el]
          exact (h.2 hall).2)
      ((frsF sel mu p P).symm (repY Y)) (fun j => by rw [ef]; exact xtRepY_int sel mu cst p.deco Y hY P hP j)
    unfold ftY
    rw [if_pos hP, if_pos hP]
    exact key
  ·
    have hPQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.mp P.2).resolve_left hP
    have hz : (algebraMap (𝓞 X.E) X.E (Pr.piT u)) ≠ 0 := fun h0 => hpi P (by
      rw [map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 X.E) X.E)] at h0
      rw [h0]
      exact zero_mem _)
    have hOk : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok ∧ Pr.piT u ∉ P.1.asIdeal :=
      ⟨d.2.til (fun Q => conj_piT_notMem hPr u Q) hpi, hpi P⟩
    have eF : frsG sel mu p' P = Sc.Fr.tfaExtZ (N_m_succ R) (d.1.liftFr ⟨P.1, Finset.mem_union_right _ hPQ⟩)
        (algebraMap (𝓞 X.E) X.E (Pr.piT u)) hz := by
      unfold frsG
      rw [dite_eq_right hP, hfr P.1 hPQ]
      unfold Sc.Fr.topFrA
      simp only [dif_pos hOk]
    have hA : prXpG X.E (R.N R.m) ∘ₗ inFr (frsF sel mu p P) (frsG sel mu p' P) x =
        (d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap := by
      rw [eF]
      refine LinearMap.ext fun v => funext fun i => ?_
      show (Sc.Fr.tfaExtZ (N_m_succ R) _ _ hz).symm (x (frsF sel mu p P v)) ⟨i.1, _⟩ = _
      rw [tq_tfaZ_symm, dif_pos (show i.1 < R.N R.m - 1 from i.2)]
      rfl
    have hB : atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ inFr (frsF sel mu p P) (frsG sel mu p' P) x =
        (((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap := by
      rw [eF]
      refine LinearMap.ext fun v => ?_
      show atNL X.E (R.N R.m) (R.N R.m - 1) ((Sc.Fr.tfaExtZ (N_m_succ R) _ _ hz).symm (x (frsF sel mu p P v))) =
        ((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ * atNL X.E (R.N R.m) (R.N R.m - 1) (x (frsF sel mu p P v))
      unfold atNL
      simp only [dif_pos hlast]
      show (Sc.Fr.tfaExtZ (N_m_succ R) _ _ hz).symm (x (frsF sel mu p P v)) ⟨R.N R.m - 1, hlast⟩ = _
      rw [tq_tfaZ_symm, dite_eq_right (show ¬ (R.N R.m - 1 < R.N R.m - 1) from lt_irrefl _)]
      rfl
    rw [show (prXpG X.E (R.N R.m) ∘ₗ inFr (frsF sel mu p P) (frsG sel mu p' P) x ∘ₗ
        LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) =
        (d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap ∘ₗ
          LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) by
      rw [← LinearMap.comp_assoc, hA]
      rfl, hB]
    unfold PhiTopG PhiTop
    (try simp only [hP, if_false])

end Fin

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.DiagUnitMemAndNormalizesKOne
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwK1b

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E))

theorem twLamQB_red_one (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {kj n' N : ℕ} (hn : n' ≤ N) (y : Sp E N ≃ₗ[E] Sp E N)
    (hent : ∀ s t : Fin N, kj ≤ s.1 → s.1 < n' → kj ≤ t.1 → t.1 < n' →
      IntAt P (y (Pi.single t 1) s) ∧ redP P (y (Pi.single t 1) s) = if s = t then 1 else 0) :
    LocE.lamQB ξ kj n' (y : Sp E N →ₗ[E] Sp E N) = 1 := by
  classical
  have hlt : ∀ u : Fin (n' - kj), kj + u.1 < N := fun u => by have := u.2; omega
  have hlt' : ∀ u : Fin (n' - kj), kj + u.1 < n' := fun u => by have := u.2; omega
  have hM : ∀ s t : Fin (n' - kj), Loc.atN ((y : Sp E N →ₗ[E] Sp E N) (Loc.eN E N (kj + t.1))) (kj + s.1)
      = y (Pi.single (⟨kj + t.1, hlt t⟩ : Fin N) 1) ⟨kj + s.1, hlt s⟩ := by
    intro s t
    have he : Loc.eN E N (kj + t.1) = Pi.single (⟨kj + t.1, hlt t⟩ : Fin N) 1 := by
      funext l
      simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
    rw [he]
    simp only [Loc.atN, dif_pos (hlt s)]
    rfl
  have hent' := fun s t : Fin (n' - kj) =>
    hent ⟨kj + s.1, hlt s⟩ ⟨kj + t.1, hlt t⟩ (by simp) (hlt' s) (by simp) (hlt' t)
  have hdet : redP P (Matrix.of fun s t : Fin (n' - kj) =>
      Loc.atN ((y : Sp E N →ₗ[E] Sp E N) (Loc.eN E N (kj + t.1))) (kj + s.1)).det = 1 := by
    rw [reduction_det_eq_det_reduction]
    · have h1 : (Matrix.of fun s t : Fin (n' - kj) =>
          redP P (Loc.atN ((y : Sp E N →ₗ[E] Sp E N) (Loc.eN E N (kj + t.1))) (kj + s.1))) = 1 := by
        ext s t
        rw [Matrix.of_apply, hM, (hent' s t).2, Matrix.one_apply]
        simp [Fin.ext_iff]
      rw [h1, Matrix.det_one]
    · intro s t
      rw [hM]
      exact (hent' s t).1
  unfold LocE.lamQB LocE.unitV
  split_ifs with hu
  · have hu1 : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hdet]; rfl)
    rw [hu1, map_one, Units.val_one, inv_one]
  · exact absurd (hdet ▸ isUnit_one) hu

theorem twRed0_of_val {w : E} (hw : P.valuation E w < 1) : IntAt P w ∧ redP P w = 0 := by
  classical
  obtain ⟨x, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) w
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsE : algebraMap (𝓞 E) E s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  obtain ⟨m, hm⟩ : ∃ m : ℕ, P.intValuation s = WithZero.exp (-(m : ℤ)) :=
    ⟨_, P.intValuation_if_neg hs0⟩
  obtain ⟨J, hJ⟩ := (P.intValuation_le_pow_iff_dvd s m).mp hm.le
  have hJP : ¬ J ≤ P.asIdeal := by
    intro hle
    have h2 : P.asIdeal ^ (m + 1) ∣ Ideal.span {s} := by
      rw [hJ, pow_succ]
      exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.mpr hle)
    have h3 := (P.intValuation_le_pow_iff_dvd s (m + 1)).mpr h2
    rw [hm, WithZero.exp_le_exp] at h3
    push_cast at h3
    omega
  obtain ⟨t, htJ, htP⟩ := SetLike.not_le_iff_exists.mp hJP
  have htE : algebraMap (𝓞 E) E t ≠ 0 := by
    have ht0 : t ≠ 0 := fun h => htP (h ▸ P.asIdeal.zero_mem)
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]
  have hx : x ∈ P.asIdeal ^ m := by
    rw [← P.intValuation_le_pow_iff_mem, ← hm, ← HeightOneSpectrum.valuation_of_algebraMap (K := E),
      ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E x) ≤ P.valuation E (algebraMap (𝓞 E) E s)
    have e : algebraMap (𝓞 E) E x = (algebraMap (𝓞 E) E x / algebraMap (𝓞 E) E s) * algebraMap (𝓞 E) E s := by
      field_simp
    rw [e, map_mul]
    exact mul_le_of_le_one_left' hw.le
  have hxt : x * t ∈ Ideal.span {s} := by
    rw [hJ]
    exact Ideal.mul_mem_mul hx htJ
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hxt
  have hz' : algebraMap (𝓞 E) E x / algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E z / algebraMap (𝓞 E) E t := by
    rw [div_eq_div_iff hsE htE, ← map_mul, ← map_mul, ← hz, mul_comm]
  have hrel : algebraMap (𝓞 E) E t * (algebraMap (𝓞 E) E x / algebraMap (𝓞 E) E s) = algebraMap (𝓞 E) E z := by
    rw [hz']
    field_simp
  have ht1 : P.valuation E (algebraMap (𝓞 E) E t) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr htP
  have hzP : z ∈ P.asIdeal := by
    rw [← P.intValuation_lt_one_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E z) < 1
    rw [← hrel, map_mul, ht1, one_mul]
    exact hw
  refine ⟨⟨z, t, htP, hrel⟩, redP_eq P htP hrel ?_⟩
  rw [mul_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
  exact hzP

end TwK1b

end Formalism.L2.Col
end
end

