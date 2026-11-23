module

public import Mathlib
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0360
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterIffIsCuspidalGLnFiniteField
section
open CategoryTheory Polynomial

noncomputable section

namespace GlobalTheory.CuspCharRep

open Formalism.IrreducibleCountingLemmas.TYPES GlobalTheory.GLq GlobalTheory.FiniteGL

variable {g : ℕ} [Fact g.Prime]

theorem mem_unipRadical_twoBlocks_iff {d a : ℕ} (had : a ≤ d) (x : Gn g d) :
    x ∈ unipRadical (ZMod g) (twoBlocks d a) ↔
      (InPar a (x : Mt g d) ∧ tl a (x : Mt g d) = 1 ∧ br a (d - a) (x : Mt g d) = 1) := by
  rw [mem_unipRadical]
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_, ?_⟩
    · have := h i j (by simp [twoBlocks]; split_ifs <;> omega)
      have hne : i ≠ j := fun e => by rw [e] at hi; omega
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at this
    · funext i j
      have := h ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp [twoBlocks, i.2, j.2])
      rw [Matrix.sub_apply, sub_eq_zero] at this
      simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (show (i : ℕ) < d ∧ (j : ℕ) < d by omega)]
      rw [this]
      simp [Matrix.one_apply, Fin.ext_iff]
    · funext i j
      have := h ⟨a + i, by omega⟩ ⟨a + j, by omega⟩ (by simp [twoBlocks])
      rw [Matrix.sub_apply, sub_eq_zero] at this
      simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (show a + (i : ℕ) < d ∧ a + (j : ℕ) < d by omega)]
      rw [this]
      simp [Matrix.one_apply, Fin.ext_iff]
  · rintro ⟨hP, htl, hbr⟩ i j hij
    rw [Matrix.sub_apply, sub_eq_zero]
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
    · have := congrFun (congrFun htl ⟨i, hi⟩) ⟨j, hj⟩
      simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (show (i : ℕ) < d ∧ (j : ℕ) < d from ⟨i.2, j.2⟩)] at this
      rw [this]
      simp [Matrix.one_apply, Fin.ext_iff]
    · exfalso
      simp [twoBlocks, hi, hj] at hij
    · have hne : i ≠ j := fun e => by rw [e] at hi; exact hi hj
      rw [hP i j hj (not_lt.1 hi), Matrix.one_apply_ne hne]
    · have := congrFun (congrFun hbr ⟨i - a, by omega⟩) ⟨j - a, by omega⟩
      simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN] at this
      rw [dif_pos (show a + ((i : ℕ) - a) < d ∧ a + ((j : ℕ) - a) < d by omega)] at this
      have ei : (⟨a + ((i : ℕ) - a), by omega⟩ : Fin d) = i := Fin.ext (by simp; omega)
      have ej : (⟨a + ((j : ℕ) - a), by omega⟩ : Fin d) = j := Fin.ext (by simp; omega)
      rw [ei, ej] at this
      rw [this, Matrix.one_apply, Matrix.one_apply]
      simp only [Fin.ext_iff]
      split_ifs with h1 h2 h2 <;> first | rfl | omega


open scoped Classical in
theorem res_one_one_eq {d a : ℕ} (had : a ≤ d) (χ : Gn g d → ℂ) :
    res a (d - a) χ 1 1 =
      ((g : ℂ) ^ (a * (d - a)))⁻¹ * ∑ u : unipRadical (ZMod g) (twoBlocks d a), χ u := by
  unfold res
  congr 1
  rw [← Finset.sum_filter]
  refine Finset.sum_subtype _ (fun x => ?_) χ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Units.val_one]
  exact (mem_unipRadical_twoBlocks_iff had x).symm


open scoped Classical in
theorem res_character_eq_zero_iff {d a : ℕ} (had : a ≤ d) (V : FDRep ℂ (Gn g d)) :
    res a (d - a) (fun x => V.character x) 1 1 = 0 ↔
      ∀ v : V, (∀ u ∈ unipRadical (ZMod g) (twoBlocks d a), V.ρ u v = v) → v = 0 := by
  rw [res_one_one_eq had, mul_eq_zero]
  have hg : ((g : ℂ) ^ (a * (d - a)))⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero))
  simp only [hg, false_or]
  have h := GlobalTheory.GoodTypeGeneric.sum_character_eq_zero_iff
    (V.ρ.comp (unipRadical (ZMod g) (twoBlocks d a)).subtype)
  have e : ∀ u : unipRadical (ZMod g) (twoBlocks d a),
      Representation.character (V.ρ.comp (unipRadical (ZMod g) (twoBlocks d a)).subtype) u = V.character u := fun u => rfl
  simp only [e] at h
  rw [h]
  constructor
  · intro H v hv
    exact H v fun u => hv u u.2
  · intro H v hv
    exact H v fun u hu => hv ⟨u, hu⟩

def cb (d a : ℕ) : Fin d → Fin 2 := fun i => if (i : ℕ) < a then 0 else 1

theorem val_cb (d a : ℕ) (i : Fin d) : ((cb d a i : Fin 2) : ℕ) = twoBlocks d a i := by
  simp only [cb, twoBlocks]
  split_ifs <;> rfl

theorem mem_unipRadical_of_mem_unip {d a : ℕ} {u : Gn g d} (hu : u ∈ unip (ZMod g) (cb d a)) :
    u ∈ unipRadical (ZMod g) (twoBlocks d a) := by
  obtain ⟨⟨hA, -⟩, hD⟩ := hu
  rw [mem_unipRadical]
  intro i j hij
  rw [Matrix.sub_apply, Matrix.one_apply]
  by_cases e : cb d a i = cb d a j
  · rw [hD i j e]
    simp
  · have hlt : cb d a j < cb d a i := by
      rw [Fin.lt_iff_val_lt_val, val_cb, val_cb]
      have e' : twoBlocks d a i ≠ twoBlocks d a j := fun h => e (Fin.ext (by rw [val_cb, val_cb, h]))
      omega
    have hne : i ≠ j := fun h => e (by rw [h])
    rw [hA i j hlt, if_neg hne, sub_zero]

theorem glEquiv_mem_unip {d a s : ℕ} (b : Fin d → Fin s) (z : Fin s) (hz : ∀ i, z ≤ b i) (σ : Fin d ≃ Fin d)
    (hσ : ∀ k : Fin d, (k : ℕ) < a ↔ b (σ k) = z) {u : Gn g d} (hu : u ∈ unipRadical (ZMod g) (twoBlocks d a)) :
    glEquiv (ZMod g) σ u ∈ unip (ZMod g) b := by
  have htb : ∀ i, twoBlocks d a (σ.symm i) = if b i = z then 0 else 1 := by
    intro i
    have h := hσ (σ.symm i)
    rw [Equiv.apply_symm_apply] at h
    simp only [twoBlocks]
    by_cases hb : b i = z
    · simp [hb, h.2 hb]
    · simp [hb, mt h.1 hb]
  have hent : ∀ w : Gn g d, w ∈ unipRadical (ZMod g) (twoBlocks d a) → ∀ i j, (b j = z ∨ b i ≠ z) →
      ((glEquiv (ZMod g) σ w : Gn g d) : Mt g d) i j = if i = j then 1 else 0 := by
    intro w hw i j hij
    rw [Formalism.L2.PT.coe_glEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]
    have h0 := (mem_unipRadical.1 hw) (σ.symm i) (σ.symm j) (by
      rw [htb, htb]
      rcases hij with h | h
      · by_cases h' : b j = z <;> simp [h, h']
      · by_cases h' : b j = z <;> simp [h, h'])
    rw [Matrix.sub_apply, sub_eq_zero, Matrix.one_apply] at h0
    rw [h0]
    simp [σ.symm.injective.eq_iff]
  have hlt : ∀ i j, b j < b i → b i ≠ z := fun i j h e => by
    have := hz j
    rw [e] at h
    exact absurd (lt_of_le_of_lt this h) (lt_irrefl _)
  have hne : ∀ i j : Fin d, b j < b i → i ≠ j := fun i j h e => by rw [e] at h; exact lt_irrefl _ h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j h
    rw [hent u hu i j (Or.inr (hlt i j h)), if_neg (hne i j h)]
  · intro i j h
    rw [← map_inv, hent u⁻¹ (inv_mem hu) i j (Or.inr (hlt i j h)), if_neg (hne i j h)]
  · intro i j h
    rw [hent u hu i j (by by_cases e : b i = z <;> simp_all)]

theorem exists_perm_first {d s : ℕ} (b : Fin d → Fin s) (z : Fin s) :
    ∃ σ : Fin d ≃ Fin d, ∀ k : Fin d, (k : ℕ) < Fintype.card {i // b i = z} ↔ b (σ k) = z := by
  classical
  set a := Fintype.card {i // b i = z} with ha
  have had : a ≤ d := (Fintype.card_subtype_le _).trans (by simp)
  have hca : Fintype.card {k : Fin d // (k : ℕ) < a} = a := by
    rw [Fintype.card_congr (show {k : Fin d // (k : ℕ) < a} ≃ Fin a from
      { toFun := fun k => ⟨k.1, k.2⟩
        invFun := fun i => ⟨⟨i, lt_of_lt_of_le i.2 had⟩, i.2⟩
        left_inv := fun k => rfl
        right_inv := fun i => rfl }), Fintype.card_fin]
  let e1 : {k : Fin d // (k : ℕ) < a} ≃ {i // b i = z} := Fintype.equivOfCardEq (by rw [hca])
  let e2 : {k : Fin d // ¬ (k : ℕ) < a} ≃ {i // ¬ b i = z} := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hca])
  refine ⟨((Equiv.sumCompl fun k : Fin d => (k : ℕ) < a).symm.trans
    ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl fun i => b i = z))), fun k => ?_⟩
  by_cases hk : (k : ℕ) < a
  · have e : ((Equiv.sumCompl fun k : Fin d => (k : ℕ) < a).symm.trans
        ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl fun i => b i = z))) k = (e1 ⟨k, hk⟩ : Fin d) := by
      simp only [Equiv.trans_apply]
      rw [Equiv.sumCompl_symm_apply_of_pos (p := fun k : Fin d => (k : ℕ) < a) hk]
      rfl
    rw [e]
    exact ⟨fun _ => (e1 ⟨k, hk⟩).2, fun _ => hk⟩
  · have e : ((Equiv.sumCompl fun k : Fin d => (k : ℕ) < a).symm.trans
        ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl fun i => b i = z))) k = (e2 ⟨k, hk⟩ : Fin d) := by
      simp only [Equiv.trans_apply]
      rw [Equiv.sumCompl_symm_apply_of_neg (p := fun k : Fin d => (k : ℕ) < a) hk]
      rfl
    rw [e]
    exact ⟨fun h => absurd h hk, fun h => absurd h (e2 ⟨k, hk⟩).2⟩

end GlobalTheory.CuspCharRep

namespace GlobalTheory.CuspCharRep

open Formalism.IrreducibleCountingLemmas.TYPES GlobalTheory.GLq GlobalTheory.FiniteGL

theorem isCusp_character_iff_isCuspidal : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))),
    1 ≤ d → CategoryTheory.Simple V →
      (GlobalTheory.GLq.IsCusp (fun x => V.character x) ↔ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V) := by
  intro g _ d V hd hV
  unfold GlobalTheory.GLq.IsCusp
  constructor
  · rintro ⟨-, -, hres⟩ s b hb hs v hv
    let z : Fin s := ⟨0, by omega⟩
    have hz : ∀ i, z ≤ b i := fun i => show (0 : ℕ) ≤ (b i : ℕ) from Nat.zero_le _
    obtain ⟨σ, hσ⟩ := exists_perm_first b z
    have ha0 : 0 < Fintype.card {i // b i = z} :=
      Fintype.card_pos_iff.2 ⟨⟨(hb z).choose, (hb z).choose_spec⟩⟩
    have had : Fintype.card {i // b i = z} < d := by
      obtain ⟨j, hj⟩ := hb ⟨1, by omega⟩
      have h := Fintype.card_subtype_lt (p := fun i => b i = z) (x := j)
        (by rw [hj]; simp [Fin.ext_iff, z])
      simpa using h
    have hw := (res_character_eq_zero_iff had.le V).1 (hres _ ha0 had)
    let P := GlobalTheory.SerOSys.TranspLabel.permGL (K := ZMod g) σ
    have key : V.ρ P⁻¹ v = 0 := hw _ fun u hu => by
      have h1 := hv _ (glEquiv_mem_unip b z hz σ hσ hu)
      have hperm : glEquiv (ZMod g) σ u = P * u * P⁻¹ := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul]
        show Matrix.reindex σ σ (u : Matrix (Fin d) (Fin d) (ZMod g)) =
          σ.symm.toPEquiv.toMatrix * (u : Matrix (Fin d) (Fin d) (ZMod g)) *
            σ.toPEquiv.toMatrix
        rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
        rfl
      rw [hperm] at h1
      calc V.ρ u (V.ρ P⁻¹ v) = V.ρ (P⁻¹ * (P * u * P⁻¹)) v := by
            rw [show P⁻¹ * (P * u * P⁻¹) = u * P⁻¹ by group, map_mul, Module.End.mul_apply]
        _ = V.ρ P⁻¹ v := by rw [map_mul, Module.End.mul_apply, h1]
    calc v = V.ρ (P * P⁻¹) v := by rw [mul_inv_cancel, map_one, Module.End.one_apply]
      _ = 0 := by rw [map_mul, Module.End.mul_apply, key, map_zero]
  · intro hc
    refine ⟨by omega, ⟨V, hV, fun _ => rfl⟩, fun a ha had => ?_⟩
    rw [res_character_eq_zero_iff had.le V]
    intro v hv
    refine hc 2 (cb d a) ?_ le_rfl v fun u hu => hv u (mem_unipRadical_of_mem_unip hu)
    intro k
    fin_cases k
    · exact ⟨⟨0, by omega⟩, by simp [cb, ha]⟩
    · exact ⟨⟨a, had⟩, by simp [cb]⟩

end GlobalTheory.CuspCharRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfLastCoordinateDilationOnePrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2.DilPt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hasRes_mk_iff {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} (r : 𝓞 E) :
    HasRes P z (Ideal.Quotient.mk P.asIdeal r) ↔ Valued.v (z - algebraMap E _ (algebraMap (𝓞 E) E r)) < 1 := by
  constructor
  · rintro ⟨r', hr', h⟩
    have hm : r' - r ∈ P.asIdeal := Ideal.Quotient.eq.1 hr'
    have h2 : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r' - r))) < 1 := by
      rw [valued_algebraMap]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hm
    have e : z - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r) =
        (z - algebraMap E _ (algebraMap (𝓞 E) E r')) + algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r' - r)) := by
      simp only [map_sub]
      ring
    rw [e]
    exact Valuation.map_add_lt _ h h2
  · intro h
    exact ⟨r, rfl, h⟩

theorem hasRes_le_one {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal}
    (h : HasRes P z c) : Valued.v z ≤ 1 := by
  obtain ⟨r, -, hr⟩ := h
  have h1 : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) ≤ 1 := by
    rw [valued_algebraMap]
    exact HeightOneSpectrum.valuation_le_one _ _
  have e : z = (z - algebraMap E _ (algebraMap (𝓞 E) E r)) + algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r) := by
    ring
  rw [e]
  exact Valuation.map_add_le _ hr.le h1

theorem hasRes_lt_one {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} (h : HasRes P z 0) : Valued.v z < 1 := by
  have := (hasRes_mk_iff (P := P) (z := z) 0).1 (by simpa using h)
  simpa using this

theorem last_sub_lt {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (r : Fin n) (Ki : Fin n → P.adicCompletion E)
    (D : Fin n → Fin n → P.adicCompletion E) (U : Fin n → P.adicCompletion E) (C : P.adicCompletion E)
    (hK : ∀ j, Valued.v (Ki j) ≤ 1) (hK' : ∀ j, j ≠ r → Valued.v (Ki j) < 1)
    (hD : ∀ j l, Valued.v (D j l) ≤ 1) (hDr : ∀ l, Valued.v (D r l - if l = r then C else 0) < 1)
    (hU : ∀ l, Valued.v (U l) ≤ 1) (hC : Valued.v C ≤ 1) :
    Valued.v ((∑ j, Ki j * ∑ l, D j l * U l) - C * ∑ j, Ki j * U j) < 1 := by
  have e : (∑ j, Ki j * ∑ l, D j l * U l) - C * ∑ j, Ki j * U j =
      ∑ j, Ki j * ((∑ l, D j l * U l) - C * U j) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
  rw [map_mul]
  by_cases hj : j = r
  · subst hj
    have e2 : (∑ l, D j l * U l) - C * U j = ∑ l, (D j l - if l = j then C else 0) * U l := by
      simp only [_root_.sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [e2]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' (hK j)) ?_
    exact Valuation.map_sum_lt _ one_ne_zero fun l _ => by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (hU l)) (hDr l)
  · refine lt_of_le_of_lt (mul_le_of_le_one_right' ?_) (hK' j hj)
    refine Valuation.map_sub _ _ _ |>.trans (max_le ?_ ?_)
    · exact Valuation.map_sum_le _ fun l _ => by
        rw [map_mul]
        exact mul_le_one' (hD j l) (hU l)
    · rw [map_mul]
      exact mul_le_one' hC (hU j)

theorem pullbackVector_triple_mul {n : ℕ} (y δ k : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (y * δ * k) x =
      ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
        (((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV y x) := by
  unfold GlobalTheory.Mem.Col2.pullV
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem pullbackVector_mul_right {n : ℕ} (y k : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (y * k) x =
      ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV y x := by
  unfold GlobalTheory.Mem.Col2.pullV
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]

theorem adAt_pullV_triv {n : ℕ} (y δ k : GL (Fin n) (AfE F E)) (w : HeightOneSpectrum (𝓞 E))
    (ht : ∀ i j, adAt F w ((δ⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if i = j then 1 else 0) (x : Sp E n) (i : Fin n) :
    adAt F w (GlobalTheory.Mem.Col2.pullV (y * δ * k) x i) = adAt F w (GlobalTheory.Mem.Col2.pullV (y * k) x i) := by
  rw [pullbackVector_triple_mul, pullbackVector_mul_right]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, ht, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem adeleComponentAt_triple_mul_dilation_trivial {n : ℕ} (y δ k : GL (Fin n) (AfE F E)) (w : HeightOneSpectrum (𝓞 E))
    (ht : ∀ i j, adAt F w ((δ⁻¹ : GL (Fin n) (AfE F E)).1 i j) = if i = j then 1 else 0) (i j : Fin n) :
    adAt F w ((y * δ * k : GL (Fin n) (AfE F E)).1 i j) = adAt F w ((y * k : GL (Fin n) (AfE F E)).1 i j) := by
  have h1 : ((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1 := by
    ext a b
    rw [Matrix.map_apply, ht, Matrix.one_apply]
  have h2 : (δ : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1 := by
    have e : (δ : Matrix (Fin n) (Fin n) (AfE F E)) * ((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have := congrArg (fun M : Matrix (Fin n) (Fin n) (AfE F E) => M.map (adAt F w)) e
    simp only [Matrix.map_mul, h1, mul_one, Matrix.map_one (adAt F w) (map_zero _) (map_one _)] at this
    exact this
  have e : ((y * δ * k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) =
      ((y * k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) := by
    simp only [Units.val_mul, Matrix.map_mul, h2, mul_one]
  exact congrArg (fun M => M i j) e

theorem isPointOf_last_coordinate_dilation_one_prime_alt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (y δ k : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q) (P : ST) (c : (𝓞 E ⧸ P.1.asIdeal)ˣ) (b : 𝓞 E ⧸ P.1.asIdeal), IsPtOf hc (y * k) p → k ∈ Formalism.L2.Herm.UstdAf hc n → δ ∈ Formalism.L2.Herm.UstdAf hc n → Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n) → (∀ i j, δ.1 i j ∈ RInt F E) → (∀ i j, (δ⁻¹).1 i j ∈ RInt F E) → (∀ w : HeightOneSpectrum (𝓞 E), (w ∈ SG ∨ w ∈ Q ∨ (w ∈ ST ∧ w ≠ P.1)) → ∀ i j, adAt F w ((δ⁻¹).1 i j) = if i = j then 1 else 0) → (∀ r j : Fin n, r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹).1 r j)) (if j = r then b else 0)) → (∀ r j : Fin n, r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((δ⁻¹).1 r j)) (if j = r then (c : 𝓞 E ⧸ P.1.asIdeal) else 0)) → p'.deco = DecoSet.dia1 P c p.deco → p'.fr = p.fr → IsPtOf hc (y * δ * k) p' := by
  intro F E _ _ _ _ _ _ hc n ST SG Q y δ k p p' P c b h hk hδ hkc hδi hδi' htriv hkr hδr hdeco hfr
  classical
  have hy : y ∈ Formalism.L2.Herm.UstdAf hc n := by
    have := mul_mem h.uni (inv_mem hk)
    rwa [mul_inv_cancel_right] at this
  have hkI : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔
      ∀ i, (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) i ∈ RInt F E :=
    fun z => (mem_latS_std z).symm.trans ((hkc z).trans (mem_latS_std _))
  have hδI : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔
      ∀ i, (((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) i ∈ RInt F E := by
    intro z
    constructor
    · intro hz i
      exact PtExist.mulVec_int hδi' hz i
    · intro hz i
      have := PtExist.mulVec_int hδi hz i
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at this
  have hN : p'.deco.1.N = p.deco.1.N := by rw [hdeco]; rfl
  have hbe : p'.deco.1.be = p.deco.1.be := by rw [hdeco]; rfl
  have hf : ∀ (P' : ST) (x : Sp E n), p'.deco.1.f P' x =
      ((Pi.mulSingle (M := fun Q : ST => (𝓞 E ⧸ Q.1.asIdeal)ˣ) P c P' : (𝓞 E ⧸ P'.1.asIdeal)ˣ) : 𝓞 E ⧸ P'.1.asIdeal) * p.deco.1.f P' x := by
    intro P' x
    rw [hdeco]
    rfl
  have hu : ∀ x ∈ p.deco.1.N, ∀ l, GlobalTheory.Mem.Col2.pullV y x l ∈ RInt F E := by
    intro x hx
    refine (hkI _).2 ?_
    rw [← pullbackVector_mul_right]
    exact (mem_latS_std _).1 ((h.lat _).1 (Submodule.subset_span ⟨x, hx, rfl⟩))
  refine ⟨mul_mem (mul_mem hy hδ) hk, fun z => ?_, fun P' x hx i hi => ?_, fun w x hx i => ?_, fun P' i j => ?_⟩
  · rw [hN]
    refine (h.lat z).trans ((mem_latS_std _).trans (Iff.trans ?_ (mem_latS_std _).symm))
    have e1 : ((y * k : GL (Fin n) (AfE F E))⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ z =
        ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          (((y⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z) := by
      rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]
    have e2 : ((y * δ * k : GL (Fin n) (AfE F E))⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ z =
        ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          (((δ⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
            (((y⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ z)) := by
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc]
    rw [e1, e2]
    exact (hkI _).symm.trans ((hδI _).trans (hkI _))
  · rw [hN] at hx
    have hv := h.f P' x hx i hi
    rw [hf]
    by_cases hPP : P' = P
    · subst hPP
      rw [Pi.mulSingle_eq_same]
      obtain ⟨s, hs, hv'⟩ := hv
      obtain ⟨cr, hcr⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 E ⧸ P'.1.asIdeal)
      rw [← hs, ← hcr, ← map_mul, hasRes_mk_iff]
      have hint : ∀ a ∈ RInt F E, Valued.v (adAt F P'.1 a) ≤ 1 := fun a ha => (mem_rInt_iff F E a).1 ha P'.1
      have hCle : Valued.v (algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E cr)) ≤ 1 := by
        rw [valued_algebraMap]
        exact HeightOneSpectrum.valuation_le_one _ _
      have key := last_sub_lt i (fun j => adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j))
        (fun j l => adAt F P'.1 ((δ⁻¹ : GL (Fin n) (AfE F E)).1 j l))
        (fun l => adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x l)) (algebraMap E _ (algebraMap (𝓞 E) E cr))
        (fun j => hasRes_le_one (hkr i j hi))
        (fun j hj => by
          have := hkr i j hi
          rw [if_neg hj] at this
          exact hasRes_lt_one this)
        (fun j l => hint _ (hδi' j l))
        (fun l => by
          have := hδr i l hi
          by_cases hl : l = i
          · rw [if_pos hl, ← hcr, hasRes_mk_iff] at this
            rw [if_pos hl]
            exact this
          · rw [if_neg hl] at this
            rw [if_neg hl, sub_zero]
            exact hasRes_lt_one this)
        (fun l => hint _ (hu x hx l)) hCle
      rw [pullbackVector_mul_right] at hv'
      rw [pullbackVector_triple_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at hv' key ⊢
      have e : (∑ j, adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) *
            ∑ l, adAt F P'.1 ((δ⁻¹ : GL (Fin n) (AfE F E)).1 j l) * adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x l)) -
          algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E cr) *
            algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E s) =
          ((∑ j, adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) *
            ∑ l, adAt F P'.1 ((δ⁻¹ : GL (Fin n) (AfE F E)).1 j l) * adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x l)) -
          algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E cr) *
            ∑ j, adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) * adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x j)) +
          algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E cr) *
            ((∑ j, adAt F P'.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 i j) * adAt F P'.1 (GlobalTheory.Mem.Col2.pullV y x j)) -
              algebraMap E (P'.1.adicCompletion E) (algebraMap (𝓞 E) E s)) := by ring
      rw [e]
      refine Valuation.map_add_lt _ key ?_
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hCle) hv'
    · rw [Pi.mulSingle_eq_of_ne hPP, Units.val_one, one_mul,
        adAt_pullV_triv y δ k P'.1 (htriv P'.1 (Or.inr (Or.inr ⟨P'.2, fun e => hPP (Subtype.ext e)⟩))) x i]
      exact hv
  · rw [hN] at hx
    rw [hbe, adAt_pullV_triv y δ k w.1 (htriv w.1 (Or.inl w.2)) x i]
    exact h.be w x hx i
  · rw [hfr, adeleComponentAt_triple_mul_dilation_trivial y δ k P'.1 (htriv P'.1 (Or.inr (Or.inl P'.2))) i j]
    exact h.fr P' i j

end GlobalTheory.Mem.Col2.DilPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiLevelPairCompatibleOfColumnLevelsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiLevelPairCompatible_of_columnLevels : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg) (iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1), I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → (∀ kv, ((plg kv : L.Pg) : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) → (∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv)) → PsiPPTie X.toD7 (lev0 I) (chr0 I) (lev1 I) (chr1 I) (eG.trans cG) := by
  first | exact @GlobalTheory.Mem.PsiTie.psiPPTie_of_levOf | exact GlobalTheory.Mem.PsiTie.psiPPTie_of_levOf | (intros; apply GlobalTheory.Mem.PsiTie.psiPPTie_of_levOf <;> assumption)
end

