module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.JetMul
public import Formalism.PeriodIntegrals.Bundle0023

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.JetRen
section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.OJ

section Rename₂

variable {Lt Lt' : Type} {N0 N1 : ℕ}

def pEmb (φ : Lt ↪ Lt') (γ : Type) : Lt × γ ↪ Lt' × γ := φ.prodMap (Function.Embedding.refl γ)

theorem pEmb_apply (φ : Lt ↪ Lt') (γ : Type) (v : Lt × γ) : pEmb φ γ v = (φ v.1, v.2) := rfl

def xzMap (φ : Lt ↪ Lt') : XZ Lt N0 N1 → XZ Lt' N0 N1 :=
  Sum.map (pEmb φ (ℕ × Fin N0)) (pEmb φ (Fin N0 × Fin N1))

def xzEmb (φ : Lt ↪ Lt') : XZ Lt N0 N1 ↪ XZ Lt' N0 N1 :=
  ⟨xzMap φ, Function.Injective.sumMap (pEmb φ _).injective (pEmb φ _).injective⟩

theorem rename_minorXZ (φ : Lt ↪ Lt') (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) :
    MvPolynomial.rename (xzMap (N0 := N0) (N1 := N1) φ) (minorXZ N0 N1 s p I) = minorXZ N0 N1 (φ s) p I := by
  unfold minorXZ
  have h := RingHom.map_det (MvPolynomial.rename (R := ℤ) (xzMap (N0 := N0) (N1 := N1) φ)).toRingHom
    (Matrix.of fun i k : Fin p => ∑ a : Fin N0,
      MvPolynomial.X (Sum.inl (s, (i : ℕ), a)) * MvPolynomial.X (Sum.inr (s, a, I k)))
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  rw [h]
  congr 1
  ext i k
  simp [xzMap, pEmb]

theorem minorXZ_supported (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) :
    minorXZ N0 N1 s p I ∈ MvPolynomial.supported ℤ (xzLetter (Lt := Lt) (N0 := N0) (N1 := N1) ⁻¹' {s}) := by
  unfold minorXZ
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem (Subalgebra.prod_mem _ fun i _ => ?_) _
  simp only [Matrix.of_apply]
  refine Subalgebra.sum_mem _ fun a _ => Subalgebra.mul_mem _ ?_ ?_
  · exact MvPolynomial.X_mem_supported.mpr (by simp [xzLetter])
  · exact MvPolynomial.X_mem_supported.mpr (by simp [xzLetter])

theorem split_embDomain (φ : Lt ↪ Lt') (μ : XZ Lt N0 N1 →₀ ℕ) :
    Finsupp.sumFinsuppEquivProdFinsupp (Finsupp.embDomain (xzEmb φ) μ) =
      (Finsupp.embDomain (pEmb φ (ℕ × Fin N0)) (Finsupp.sumFinsuppEquivProdFinsupp μ).1,
        Finsupp.embDomain (pEmb φ (Fin N0 × Fin N1)) (Finsupp.sumFinsuppEquivProdFinsupp μ).2) := by
  refine Prod.ext ?_ ?_
  · ext y
    rw [Finsupp.fst_sumFinsuppEquivProdFinsupp]
    by_cases hy : y ∈ Set.range (pEmb φ (ℕ × Fin N0))
    · obtain ⟨y0, rfl⟩ := hy
      rw [Finsupp.embDomain_apply_self, Finsupp.fst_sumFinsuppEquivProdFinsupp,
        show (Sum.inl (pEmb φ (ℕ × Fin N0) y0) : XZ Lt' N0 N1) = xzEmb φ (Sum.inl y0) from rfl,
        Finsupp.embDomain_apply_self]
    · rw [Finsupp.embDomain_of_notMem_range _ _ _ hy, Finsupp.embDomain_of_notMem_range]
      rintro ⟨x, hx⟩
      cases x with
      | inl x => exact hy ⟨x, Sum.inl_injective hx⟩
      | inr x => cases hx
  · ext y
    rw [Finsupp.snd_sumFinsuppEquivProdFinsupp]
    by_cases hy : y ∈ Set.range (pEmb φ (Fin N0 × Fin N1))
    · obtain ⟨y0, rfl⟩ := hy
      rw [Finsupp.embDomain_apply_self, Finsupp.snd_sumFinsuppEquivProdFinsupp,
        show (Sum.inr (pEmb φ (Fin N0 × Fin N1) y0) : XZ Lt' N0 N1) = xzEmb φ (Sum.inr y0) from rfl,
        Finsupp.embDomain_apply_self]
    · rw [Finsupp.embDomain_of_notMem_range _ _ _ hy, Finsupp.embDomain_of_notMem_range]
      rintro ⟨x, hx⟩
      cases x with
      | inl x => cases hx
      | inr x => exact hy ⟨x, Sum.inr_injective hx⟩

variable [Fintype Lt] [DecidableEq Lt] [Fintype Lt'] [DecidableEq Lt'] (l : ℕ) [Fact l.Prime]

theorem applyTerm_rename (φ : Lt ↪ Lt') (T : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (μ : XZ Lt N0 N1 →₀ ℕ) (c : ℤ) :
    applyTerm l (MvPowerSeries.rename (pEmb φ (Fin N0 × Fin N1)) T) (Finsupp.embDomain (xzEmb φ) μ) c =
      MvPolynomial.rename (pEmb φ (ℕ × Fin N0)) (applyTerm l T μ c) := by
  unfold applyTerm
  rw [split_embDomain, MvPolynomial.rename_monomial, ← Finsupp.embDomain_eq_mapDomain]
  congr 2
  · rw [Finsupp.prod_embDomain]
  · exact MvPowerSeries.coeff_embDomain_rename _ _ _

theorem applyAt0_rename (φ : Lt ↪ Lt') (T : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) :
    applyAt0 N0 N1 l (MvPowerSeries.rename (pEmb φ (Fin N0 × Fin N1)) T) (MvPolynomial.rename (xzMap φ) P) =
      MvPolynomial.rename (pEmb φ (ℕ × Fin N0)) (applyAt0 N0 N1 l T P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial μ c =>
    rw [MvPolynomial.rename_monomial, applyAt0_monomial, applyAt0_monomial,
      show Finsupp.mapDomain (xzMap φ) μ = Finsupp.embDomain (xzEmb φ) μ from
        (Finsupp.embDomain_eq_mapDomain (xzEmb φ) μ).symm]
    exact applyTerm_rename l φ T μ c
  | add P Q hP hQ => rw [map_add (f := _), applyAt0_add, applyAt0_add, hP, hQ, map_add (f := _)]

end Rename₂

theorem serIn_rename {Lt Lt' γ K : Type*} [CommSemiring K] (φ : Lt ↪ Lt') (T : MvPowerSeries (Lt × γ) K) :
    SerIn {v : Lt' × γ | v.1 ∈ Set.range φ}
      (MvPowerSeries.rename (φ.prodMap (Function.Embedding.refl γ)) T) := by
  intro ν hν v hv
  by_contra hvr
  apply hν
  apply MvPowerSeries.coeff_rename_eq_zero
  rintro ⟨ν', rfl⟩
  rw [← Finsupp.embDomain_eq_mapDomain] at hv
  by_cases h : v ∈ Set.range (φ.prodMap (Function.Embedding.refl γ))
  · obtain ⟨w, rfl⟩ := h
    exact hvr ⟨w.1, rfl⟩
  · exact hv (Finsupp.embDomain_of_notMem_range _ _ _ h)

theorem norm_coeff_rename_le {σ τ K : Type*} [NormedCommRing K] (f : σ ↪ τ) (A : MvPolynomial σ K) {b : ℝ}
    (hb : 0 ≤ b) (hA : ∀ m, ‖AddMonoidAlgebra.coeff A m‖ ≤ b) (m : τ →₀ ℕ) :
    ‖AddMonoidAlgebra.coeff (MvPolynomial.rename f A) m‖ ≤ b := by
  by_cases h : ∃ m', Finsupp.mapDomain f m' = m
  · obtain ⟨m', rfl⟩ := h
    rw [MvPolynomial.coeff_rename_mapDomain f f.injective]
    exact hA m'
  · rw [MvPolynomial.coeff_rename_eq_zero f A m (fun u hu => absurd ⟨u, hu⟩ h)]
    simpa using hb

end PI.OrbJet.OJ

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.OrbEmb
section
noncomputable section

open Classical

namespace PI.OrbJet.OrbW

open Formalism.BasicNotions Formalism.MainNotions.G MvPowerSeries Finsupp PI.OrbJet

theorem orbMap_inj (D : D7) (p : ℕ) (z : Pl D) : Function.Injective (orbMap D p z) := by
  intro s t h
  exact ZMod.val_injective _ (posPl_inj D p z s.val t.val (ZMod.val_lt s) (ZMod.val_lt t) h)

def orbEmb (D : D7) (p : ℕ) (z : Pl D) (β : Type) : ZMod (nP D p) × β ↪ Pl D × β :=
  ⟨fun v => (orbMap D p z v.1, v.2), fun v w h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (orbMap_inj D p z h.1) h.2⟩

theorem orbEmb_apply (D : D7) (p : ℕ) (z : Pl D) (β : Type) (v : ZMod (nP D p) × β) :
    orbEmb D p z β v = (orbMap D p z v.1, v.2) := rfl

theorem restr_eq_killCompl (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (z : Pl D)
    (Th : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) :
    restr D p z Th = killCompl (orbEmb D p z (Fin N0 × Fin N1)) Th := by
  funext m
  change _ = coeff m (killCompl (orbEmb D p z (Fin N0 × Fin N1)) Th)
  rw [coeff_killCompl]
  unfold restr
  rw [Finsupp.embDomain_eq_mapDomain]
  rfl

theorem natCast_val_add_mul (n : ℕ) [NeZero n] (s : ZMod n) (e : ℕ) :
    ((s.val + e * (n - 1) : ℕ) : ZMod n) = s - e := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hn, ZMod.natCast_self, Nat.cast_one,
    ZMod.natCast_zmod_val]
  ring

theorem posPl_eq_orbMap (D : D7) (p : ℕ) (z : Pl D) (k : ℕ) :
    posPl D p z k = orbMap D p z (k : ZMod (nP D p)) := by
  show posPl D p z k = posPl D p z ((k : ZMod (nP D p)).val)
  rw [ZMod.val_natCast, posPl_mod]

theorem backPl_orbMap (D : D7) (p : ℕ) (z : Pl D) (s : ZMod (nP D p)) (e : ℕ) :
    backPl D p (orbMap D p z s) e = orbMap D p z (s - e) := by
  have h := posPl_eq_orbMap D p z (s.val + e * (nP D p - 1))
  rw [natCast_val_add_mul] at h
  show posPl D p (posPl D p z s.val) (e * (nP D p - 1)) = orbMap D p z (s - e)
  rw [posPl_add]
  exact h

theorem orbit_of_backPl (D : D7) (p : ℕ) (z y : Pl D) (s : ZMod (nP D p)) (e : ℕ)
    (h : backPl D p y e = orbMap D p z s) : ∃ s', orbMap D p z s' = y := by
  refine ⟨s + e, ?_⟩
  have h3 : e * (nP D p - 1) + e = e * nP D p := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne (nP D p))
    rw [hk, Nat.succ_sub_one, Nat.mul_succ]
  have h1 : posPl D p (backPl D p y e) e = y := by
    unfold backPl
    rw [posPl_add, h3, ← posPl_mod, Nat.mul_mod_left, posPl_zero]
  have h2 : posPl D p (orbMap D p z s) e = orbMap D p z (s + e) := by
    show posPl D p (posPl D p z s.val) e = _
    rw [posPl_add, posPl_eq_orbMap]
    congr 1
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
  calc orbMap D p z (s + e) = posPl D p (orbMap D p z s) e := h2.symm
    _ = posPl D p (backPl D p y e) e := by rw [h]
    _ = y := h1

theorem JetTdeg_embDomain {σ τ : Type*} (f : σ ↪ τ) (m : σ →₀ ℕ) : JetTdeg (embDomain f m) = JetTdeg m := by
  unfold JetTdeg
  rw [Finsupp.sum_embDomain]

theorem killCompl_logPl_emb (D : D7) (p : ℕ) [Fact p.Prime] {β : Type} (z : Pl D) (w : ZMod (nP D p) × β) :
    killCompl (orbEmb D p z β) (logPl D p (orbEmb D p z β w)) = jetLogG p (nP D p) w := by
  have key : ∀ e : ℕ, ((backPl D p (orbEmb D p z β w).1 (2 * e), (orbEmb D p z β w).2) : Pl D × β)
      = orbEmb D p z β (w.1 - 2 * (e : ZMod (nP D p)), w.2) := by
    intro e
    rw [orbEmb_apply, orbEmb_apply]
    simp only [backPl_orbMap, Nat.cast_mul, Nat.cast_ofNat]
  funext m
  change coeff m (killCompl (orbEmb D p z β) (logPl D p (orbEmb D p z β w))) = _
  rw [coeff_killCompl]
  show logPl D p (orbEmb D p z β w) (embDomain (orbEmb D p z β) m) = jetLogG p (nP D p) w m
  simp only [logPl, jetLogG, JetTdeg_embDomain]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases hm : m = Finsupp.single (w.1 - 2 * (e : ZMod (nP D p)), w.2) ((p ^ 2) ^ e)
  · rw [if_pos hm, if_pos]
    rw [key e, hm, Finsupp.embDomain_single]
  · rw [if_neg hm, if_neg]
    intro h'
    apply hm
    rw [key e, ← Finsupp.embDomain_single] at h'
    exact Finsupp.embDomain_injective _ h'

theorem killCompl_logPl_off (D : D7) (p : ℕ) [Fact p.Prime] {β : Type} (z : Pl D) (v : Pl D × β)
    (hv : ¬ ∃ w, orbEmb D p z β w = v) : killCompl (orbEmb D p z β) (logPl D p v) = 0 := by
  funext m
  change coeff m (killCompl (orbEmb D p z β) (logPl D p v)) = 0
  rw [coeff_killCompl]
  show logPl D p v (embDomain (orbEmb D p z β) m) = 0
  simp only [logPl]
  refine Finset.sum_eq_zero (fun e _ => ?_)
  rw [if_neg]
  intro h'
  apply hv
  have hk : (p ^ 2) ^ e ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hmem : (backPl D p v.1 (2 * e), v.2) ∈ (embDomain (orbEmb D p z β) m).support := by
    rw [h', Finsupp.support_single_ne_zero _ hk]
    exact Finset.mem_singleton_self _
  rw [Finsupp.support_embDomain] at hmem
  obtain ⟨a, -, ha⟩ := Finset.mem_map.mp hmem
  rw [orbEmb_apply] at ha
  obtain ⟨s', hs'⟩ := orbit_of_backPl D p z v.1 a.1 (2 * e) (Prod.ext_iff.mp ha).1.symm
  exact ⟨(s', v.2), by rw [orbEmb_apply]; exact Prod.ext hs' rfl⟩

end PI.OrbJet.OrbW
end
end

