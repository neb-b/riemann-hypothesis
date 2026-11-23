module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousActP
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIrreducibleBaseChangeWeightTensorDualRepOfEmbe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0368
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCoefficientCompatibility
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2.BasePoint

open GlobalTheory.Mem.Col2.PtExist

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

private lemma mem_divs_iff' {E : Type} [Field E] [NumberField E] {π : 𝓞 E} {P : HeightOneSpectrum (𝓞 E)}
    (h : P ∈ divs π) : π ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · simpa using h
  · simp at h

private lemma false_of_mem_of_conj_mem_of_isCoprime {E : Type} [Field E] [NumberField E] [StarRing E] {π : 𝓞 E} (hcp : IsCoprime π (cO E π))
    (P : HeightOneSpectrum (𝓞 E)) (h1 : π ∈ P.asIdeal) (h2 : cO E π ∈ P.asIdeal) : False := by
  obtain ⟨u, v, h⟩ := hcp
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

private lemma valued_algebraMap_int_le_one' {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) ≤ 1 := by
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one P r

private lemma valued_algebraMap_eq_one_of_not_mem {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E)
    (hr : r ∉ P.asIdeal) : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) = 1 := by
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation, HeightOneSpectrum.valuation_of_algebraMap]
  have h2 : ¬ P.intValuation r < 1 := fun h => hr ((HeightOneSpectrum.intValuation_lt_one_iff_mem P r).1 h)
  exact le_antisymm (HeightOneSpectrum.intValuation_le_one P r) (not_lt.1 h2)

private lemma valued_inv_algebraMap_le_one_of_not_mem {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E)
    (hr : r ∉ P.asIdeal) : Valued.v (algebraMap E (P.adicCompletion E) ((algebraMap (𝓞 E) E r)⁻¹)) ≤ 1 := by
  rw [map_inv₀, map_inv₀, valued_algebraMap_eq_one_of_not_mem P r hr, inv_one]

private lemma mem_RInt_of_valued_le_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (y : AfE F E)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (adAt F P y) ≤ 1) : y ∈ RInt F E :=
  (GlobalTheory.Mem.Col2.mem_rInt_iff F E y).2 h

theorem exists_unit (hc : Formalism.BasicNotions.CMData F E) {π : 𝓞 E} (h0 : π ≠ 0) (h1 : cO E π ≠ 0) (hcp : IsCoprime π (cO E π)) :
    ∃ a a' : AfE F E, a' * a = 1 ∧ sigR hc.sig (FiniteAdeleRing (𝓞 F) F) a = a' ∧ a ∈ RInt F E ∧ a' ∈ RInt F E ∧
      (∀ P ∈ divs π, adAt F P a' = algebraMap E _ (algebraMap (𝓞 E) E (cO E π))) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), π * cO E π ∉ w.asIdeal → adAt F w a = 1 := by
  classical
  have hmem : ∀ {P : HeightOneSpectrum (𝓞 E)}, P ∈ divs π → π ∈ P.asIdeal := fun h => mem_divs_iff' h
  have hQ : ∀ P ∈ divs π, conjPrime₂ P ∉ divs π := by
    intro P hP hP'
    exact false_of_mem_of_conj_mem_of_isCoprime hcp P (hmem hP) ((mem_conjP P π).1 (hmem hP'))
  have hc0 : (algebraMap (𝓞 E) E (cO E π)) ≠ 0 := by
    intro h
    exact h1 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).1 h)
  have hst : star (algebraMap (𝓞 E) E (cO E π)) = algebraMap (𝓞 E) E π := by
    change star (starRingEnd E (algebraMap (𝓞 E) E π)) = _
    rw [starRingEnd_apply, star_star]
  let α : HeightOneSpectrum (𝓞 E) → E := fun _ => (algebraMap (𝓞 E) E (cO E π))⁻¹
  let β : HeightOneSpectrum (𝓞 E) → E := fun _ => algebraMap (𝓞 E) E (cO E π)
  let a := GlobalTheory.Mem.Col2.PtExist.glue hc (divs π) 1 α β
  have ha : ∀ w, adAt F w a = if w ∈ divs π then algebraMap E _ (α w)
      else if conjPrime₂ w ∈ divs π then algebraMap E _ (star (β (conjPrime₂ w))) else 1 := fun w => by
    rw [GlobalTheory.Mem.Col2.PtExist.adAt_glue hc (divs π) hQ 1 α β w, map_one]
  have ha' : ∀ w, adAt F w (sigR hc.sig (FiniteAdeleRing (𝓞 F) F) a) = if w ∈ divs π then algebraMap E _ (β w)
      else if conjPrime₂ w ∈ divs π then algebraMap E _ (star (α (conjPrime₂ w))) else 1 := fun w => by
    rw [GlobalTheory.Mem.Col2.PtExist.sig_glue hc (divs π) 1 α β, map_one,
      GlobalTheory.Mem.Col2.PtExist.adAt_glue hc (divs π) hQ 1 β α w, map_one]
  refine ⟨a, sigR hc.sig (FiniteAdeleRing (𝓞 F) F) a, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · apply GlobalTheory.Mem.Col2.PtExist.ad_ext
    intro w
    rw [map_mul, ha, ha', map_one]
    split_ifs with hw hw'
    · rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
    · rw [← map_mul, star_inv₀, inv_mul_cancel₀ (star_ne_zero.2 hc0), map_one]
    · rw [mul_one]
  · apply mem_RInt_of_valued_le_one
    intro P
    rw [ha]
    split_ifs with hw hw'
    · exact valued_inv_algebraMap_le_one_of_not_mem P _ (fun h => false_of_mem_of_conj_mem_of_isCoprime hcp P (hmem hw) h)
    · rw [hst]
      exact valued_algebraMap_int_le_one' P π
    · rw [map_one]
  · apply mem_RInt_of_valued_le_one
    intro P
    rw [ha']
    split_ifs with hw hw'
    · exact valued_algebraMap_int_le_one' P _
    · rw [star_inv₀, hst]
      exact valued_inv_algebraMap_le_one_of_not_mem P π (fun h => false_of_mem_of_conj_mem_of_isCoprime hcp P h ((mem_conjP P π).1 (hmem hw')))
    · rw [map_one]
  · intro P hP
    rw [ha', if_pos hP]
  · intro w hw
    rw [ha]
    split_ifs with h2 h3
    · exact absurd (Ideal.mul_mem_right _ _ (hmem h2)) hw
    · exact absurd (Ideal.mul_mem_left _ _ ((mem_conjP w π).1 (hmem h3))) hw
    · rfl

def stdPt (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) : DecoF E n ∅ ∅ ∅ :=
  ⟨(⟨⟨stdLat E n, fun _ _ => 0, fun _ _ _ => 0⟩, stdLat_lattice, stdLat_unimodular,
      fun P => (Finset.notMem_empty _ P.2).elim, fun P => (Finset.notMem_empty _ P.2).elim,
      fun P => (Finset.notMem_empty _ P.2).elim, fun P => (Finset.notMem_empty _ P.2).elim,
      fun P => (Finset.notMem_empty _ P.2).elim, fun P => (Finset.notMem_empty _ P.2).elim,
      fun P => (Finset.notMem_empty _ P.2).elim, fun P => (Finset.notMem_empty _ P.2).elim,
      fun P => (Finset.notMem_empty _ P.2).elim⟩, fun _ => 1), fun P => (Finset.notMem_empty _ P.2).elim⟩

theorem exists_base (hc : Formalism.BasicNotions.CMData F E) {π : 𝓞 E} {T : ℕ} (hT : T ≠ 0) (hπ : π * cO E π = T)
    (hcp : IsCoprime π (cO E π)) (n : ℕ) :
    ∃ k : GL (Fin n) (AfE F E), (∃ p : DecoF E n ∅ ∅ ∅, IsPtOf hc k p ∧ p.deco.1.N = stdLat E n) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) k = 1) ∧
      ∀ (P : divs π) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹).1 r j))
        (if j = r then Ideal.Quotient.mk P.1.asIdeal (cO E π) else 0) := by
  classical
  have hT0 : ((T : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have h0 : π ≠ 0 := fun h => hT0 (by rw [← hπ, h, zero_mul])
  have h1 : cO E π ≠ 0 := fun h => hT0 (by rw [← hπ, h, mul_zero])
  obtain ⟨a, a', haa, hσ, hai, hai', hP, hw⟩ := exists_unit hc h0 h1 hcp
  let d : Fin n → AfE F E := fun i => if i.1 + 1 = n then a else 1
  let d' : Fin n → AfE F E := fun i => if i.1 + 1 = n then a' else 1
  have hd : ∀ i, d' i * d i = 1 := fun i => by
    simp only [d, d']
    split_ifs
    · exact haa
    · exact mul_one 1
  have hd' : ∀ i, d i * d' i = 1 := fun i => by rw [mul_comm]; exact hd i
  have hdi : ∀ i, d i ∈ RInt F E := fun i => by
    simp only [d]
    split_ifs
    · exact hai
    · exact one_mem _
  have hdi' : ∀ i, d' i ∈ RInt F E := fun i => by
    simp only [d']
    split_ifs
    · exact hai'
    · exact one_mem _
  let k : GL (Fin n) (AfE F E) := ⟨Matrix.diagonal d, Matrix.diagonal d',
    by rw [Matrix.diagonal_mul_diagonal]; simp only [hd']; exact Matrix.diagonal_one,
    by rw [Matrix.diagonal_mul_diagonal]; simp only [hd]; exact Matrix.diagonal_one⟩
  have hk : ((k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = Matrix.diagonal d := rfl
  have hk' : ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = Matrix.diagonal d' := rfl
  refine ⟨k, ⟨stdPt E n, ?_, rfl⟩, ?_, ?_⟩
  · constructor
    · apply (GlobalTheory.Mem.Col2.PtExist.mem_uad_iff k).2
      unfold Formalism.UG.cT
      rw [hk, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
        ← Matrix.diagonal_one]
      congr 1
      funext i
      dsimp [d]
      split_ifs
      · rw [hσ, haa]
      · rw [map_one, one_mul]
    · intro x
      unfold Formalism.L2.Herm.hatL
      change x ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (Formalism.L2.Col.stdLat E n) ↔ _
      rw [Formalism.L2.Col.mem_latS_std, Formalism.L2.Col.mem_latS_std, hk']
      constructor
      · intro h i
        rw [Matrix.mulVec_diagonal]
        exact mul_mem (hdi' i) (h i)
      · intro h i
        have := mul_mem (hdi i) (h i)
        rwa [Matrix.mulVec_diagonal, ← mul_assoc, hd' i, one_mul] at this
    all_goals intro P; exact (Finset.notMem_empty _ P.2).elim
  · intro v hv
    have hpa : prV (E := E) v a = 1 := by
      have h := ((GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E v (a - 1)).1).2 (fun w hwv => by
        have hnot : π * cO E π ∉ w.asIdeal := by
          intro hmw
          apply hv
          rw [← hwv]
          change algebraMap (𝓞 F) (𝓞 E) (T : 𝓞 F) ∈ w.asIdeal
          rw [map_natCast, ← hπ]
          exact hmw
        rw [map_sub, hw w hnot, map_one, sub_self])
      rwa [map_sub, map_one, sub_eq_zero] at h
    apply Units.ext
    rw [Units.val_one]
    change (Matrix.diagonal d).map (prV (E := E) v) = 1
    rw [Matrix.diagonal_map (map_zero _), ← Matrix.diagonal_one]
    congr 1
    funext i
    dsimp [d]
    split_ifs
    · exact hpa
    · exact map_one _
  · intro P r j hr
    rw [hk']
    unfold HasRes
    by_cases hj : j = r
    · subst hj
      rw [Matrix.diagonal_apply_eq, if_pos rfl]
      simp only [d', if_pos hr]
      rw [hP P.1 P.2]
      exact ⟨cO E π, rfl, by rw [sub_self, map_zero]; exact zero_lt_one⟩
    · rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), if_neg hj, map_zero]
      exact ⟨0, map_zero _, by rw [map_zero, map_zero, sub_self, map_zero]; exact zero_lt_one⟩

end General

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem exists_kStd : ∀ {B : Base} (X : PreX B.toPre), (B.primes X).Ok → ∀ (u : B.Word) (n : ℕ), ∃ k : GA B n, (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n) ∧ (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) k = 1) ∧ ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B n).1 r j)) (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0) := by
  intro B X hX u n
  exact exists_base B.sp.cm (π := X.piT u) (T := B.T u) (hX.T_prime u).ne_zero (hX.piT_norm u) (hX.piT_cop u) n

end GlobalTheory.Mem.Col2.BasePoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLExistsBaseChangeCoordinates
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory

theorem formsL_exists_baseChange_coordinates : ∀ {L L' Ks : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Field Ks] [NumberField Ks] [Algebra Ks L] [Algebra Ks L'] (ι : L →+* L'), (∀ y : Ks, ι (algebraMap Ks L y) = algebraMap Ks L' y) → ∀ (n : ℕ) (W : (L →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] (G : Type) [Group G] (F : Formalism.IndefR.Arith.FormsL L Ks (Fin n → L) W G),
  ∃ F' : Formalism.IndefR.Arith.FormsL L' Ks (Fin n → L') (fun σ' => W (σ'.comp ι)) G,
    (∀ (σ' : L' →+* ℂ) (x : Fin n → L), F'.j σ' (fun k => ι (x k)) = F.j (σ'.comp ι) x) ∧
    (∀ x' : Fin n → L', x' ∈ F'.WK ↔ ∃ x ∈ F.WK, x' = fun k => ι (x k)) ∧
    (∀ g, ((F'.chi g : L'ˣ) : L') = ι ((F.chi g : Lˣ) : L)) ∧
    (∀ g (x : Fin n → L), F'.ρ g (fun k => ι (x k)) = fun k => ι (F.ρ g x k)) ∧
    F'.Pt = F.Pt ∧
    ∀ lp (y' : F'.Pt lp) (y : F.Pt lp), HEq y' y → ∀ (φ' : F'.WK) (φ : F.WK), (φ'.1 = fun k => ι (φ.1 k)) → F'.nrm lp y' φ' = F.nrm lp y φ := by
  intro L L' Ks _ _ _ _ _ _ _ _ ι hι n W _ _ G _ F
  let m : (Fin n → L) →ₗ[Ks] (Fin n → L') :=
    { toFun := fun x k => ι (x k)
      map_add' := fun x y => by funext k; simp
      map_smul' := fun c x => by
        funext k
        simp only [Pi.smul_apply, RingHom.id_apply, Algebra.smul_def, map_mul, hι] }
  have minj : Function.Injective m := by
    intro x y h
    funext k
    exact ι.injective (congrFun h k)
  let e := Submodule.equivMapOfInjective m minj F.WK
  let ρ' : G →* ((Fin n → L') →ₗ[L'] (Fin n → L')) :=
    (Matrix.toLinAlgEquiv' (R := L') (n := Fin n)).toMonoidHom.comp
      ((ι.mapMatrix (m := Fin n)).toMonoidHom.comp
        ((LinearMap.toMatrixAlgEquiv' (R := L) (n := Fin n)).toMonoidHom.comp F.ρ))
  let j' : ∀ σ' : L' →+* ℂ, (Fin n → L') →ₛₗ[σ'] W (σ'.comp ι) := fun σ' =>
    { toFun := fun x' => ∑ k, σ' (x' k) • F.j (σ'.comp ι) (Pi.single k 1)
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum] }
  let F' : Formalism.IndefR.Arith.FormsL L' Ks (Fin n → L') (fun σ' => W (σ'.comp ι)) G :=
    { WK := F.WK.map m
      Pt := F.Pt
      nrm := fun lp y φ' => F.nrm lp y (e.symm φ')
      nrm_nonneg := fun lp y f => F.nrm_nonneg lp y _
      nrm_zero := fun lp y => by rw [e.symm.map_zero]; exact F.nrm_zero lp y
      nrm_add := fun lp y f g => by rw [e.symm.map_add]; exact F.nrm_add lp y _ _
      nrm_smul := fun lp y a f => by rw [e.symm.map_smul]; exact F.nrm_smul lp y a _
      towKs := inferInstance
      ρ := ρ'
      chi := (Units.map ι.toMonoidHom).comp F.chi
      j := j' }
  refine ⟨F', ?_, ?_, ?_, ?_, rfl, ?_⟩
  · intro σ' x
    have hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → L) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    show ∑ k, σ' (ι (x k)) • F.j (σ'.comp ι) (Pi.single k 1) = F.j (σ'.comp ι) x
    conv_rhs => rw [hx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, RingHom.comp_apply]
  · intro x'
    show x' ∈ F.WK.map m ↔ _
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · intro g; rfl
  · intro g x
    show Matrix.toLin' ((LinearMap.toMatrix' (F.ρ g)).map ι) (fun k => ι (x k)) = _
    funext k
    rw [Matrix.toLin'_apply]
    have := RingHom.map_mulVec ι (LinearMap.toMatrix' (F.ρ g)) x k
    rw [LinearMap.toMatrix'_mulVec] at this
    exact this.symm
  · intro lp y' y hy φ' φ hφ
    have hyy : y' = y := eq_of_heq hy
    subst hyy
    show F.nrm lp y' (e.symm φ') = F.nrm lp y' φ
    have : φ' = e φ := Subtype.ext hφ
    rw [this, LinearEquiv.symm_apply_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameComponentEqOneOffSplitPlaceOfTrivOutside
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FrameOffPlace

theorem swap_one_tmul_apply {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (ι : E ⊗[F1] FiniteAdeleRing (𝓞 F1) F1 →+* FiniteAdeleRing (𝓞 E) E)
    (hι : ∀ x a, ι (x ⊗ₜ[F1] a) = algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap F1 E a)
    (a : FiniteAdeleRing (𝓞 F2) F2) (Q : HeightOneSpectrum (𝓞 E)) :
    ι (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E
        ((GlobalTheory.Mem.R3.swapCast h).symm ((1 : E) ⊗ₜ[F2] a))) Q =
      GlobalTheory.AdeleBaseChange.locMap F2 Q (a (Q.under (𝓞 F2))) := by
  subst h
  have e : (GlobalTheory.Mem.R3.swapCast (rfl : F1 = F1)).symm ((1 : E) ⊗ₜ[F1] a) = a ⊗ₜ[F1] (1 : E) := by
    apply (GlobalTheory.Mem.R3.swapCast (rfl : F1 = F1)).injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  rw [e, Algebra.TensorProduct.comm_tmul, hι, map_one, one_mul, GlobalTheory.AdeleBaseChange.adMap_apply]

end GlobalTheory.FrameOffPlace

namespace GlobalTheory.FrameOffPlace


set_option maxHeartbeats 1000000 in
theorem cpt_conj_finE_eq_one : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E) (κ : Formalism.AUTREP.GAf D.host.E n), TrivOutside {s.v} κ → ∀ (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ s.v.asIdeal → ∀ (a b : Fin V.rank), GlobalTheory.StdFrames.cpt Q ((β⁻¹ * finE V (P.ψ κ) * β).val a b) = GlobalTheory.StdFrames.cpt Q ((1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b) := by
  classical
  intro D V n hF P β hP s κ hκ Q hQ a b
  obtain ⟨⟨β0, β0', h1, -, hβ⟩, -⟩ := hP
  let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) := Q.under _
  have hvs : v ∉ ({s.v} : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) := by
    intro h
    exact hQ (congrArg HeightOneSpectrum.asIdeal (Set.mem_singleton_iff.1 h))
  let f : ReciprocityTheory.Aut.AL D.host.E →+* Q.adicCompletion D.host.E :=
    (GlobalTheory.StdFrames.cpt Q).comp ((Formalism.IndefR.Lev.swapAE D).comp (GlobalTheory.Mem.R3.swapCast hF).symm.toRingHom)
  have hf0 : ∀ c : ReciprocityTheory.Aut.AFplus D.host.E, ReciprocityTheory.Aut.evalAt D.host.E v c = 0 →
      f ((1 : D.host.E) ⊗ₜ c) = 0 := by
    intro c hc
    have e := swap_one_tmul_apply hF (GlobalTheory.StdFrames.toAd D) (GlobalTheory.StdFrames.toAd_spec D) c Q
    have e' : f ((1 : D.host.E) ⊗ₜ c) = GlobalTheory.AdeleBaseChange.locMap _ Q (c (Q.under _)) := e
    rw [e']
    change GlobalTheory.AdeleBaseChange.locMap _ Q (ReciprocityTheory.Aut.evalAt D.host.E v c) = 0
    rw [hc, map_zero]
  have hsurj : Function.Surjective (ReciprocityTheory.Aut.evalAt D.host.E v) := fun c =>
    ⟨⟨Pi.single v c, (Filter.eventually_cofinite_ne v).mono fun w hw => by
      rw [Pi.single_eq_of_ne hw]; exact zero_mem _⟩, by
      change Pi.single v c v = c
      rw [Pi.single_eq_same]⟩
  have hker : ∀ y y' : ReciprocityTheory.Aut.AL D.host.E,
      ReciprocityTheory.Aut.compAt D.host.E v y = ReciprocityTheory.Aut.compAt D.host.E v y' → f y = f y' := by
    intro y y' h
    have hm : y - y' ∈ RingHom.ker
        (Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield D.host.E) D.host.E) (ReciprocityTheory.Aut.evalAt D.host.E v)) := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      exact h
    rw [Algebra.TensorProduct.lTensor_ker _ hsurj] at hm
    have hle : RingHom.ker (ReciprocityTheory.Aut.evalAt D.host.E v) ≤ (RingHom.ker f).comap
        (Algebra.TensorProduct.includeRight : ReciprocityTheory.Aut.AFplus D.host.E →ₐ[maximalRealSubfield D.host.E] ReciprocityTheory.Aut.AL D.host.E) := by
      intro c hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact hf0 c hc
    have h2 := Ideal.map_le_iff_le_comap.2 hle hm
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h2
    exact h2
  have hK : (κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map f = 1 := by
    have e := hκ v hvs
    ext i j
    have e2 := congrFun (congrFun e i) j
    rw [Matrix.map_apply] at e2 ⊢
    rw [Matrix.one_apply] at e2 ⊢
    split_ifs at e2 ⊢
    · rw [hker _ 1 (e2.trans (map_one _).symm), map_one]
    · rw [hker _ 0 (e2.trans (map_zero _).symm), map_zero]
  let g : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) →+* Q.adicCompletion D.host.E :=
    (GlobalTheory.StdFrames.cpt Q).comp (Formalism.IndefR.Lev.swapAE D)
  have hmain : (Formalism.IndefR.Lev.finE V (P.ψ κ)).val.map (GlobalTheory.StdFrames.cpt Q) = 1 := by
    have e1 : (Formalism.IndefR.Lev.finE V (P.ψ κ)).val = (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (P.ψ κ)).map (Formalism.IndefR.Lev.swapAE D) := rfl
    have e2 : ∀ {k l : Type} (M : Matrix k l (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)),
        (M.map (Formalism.IndefR.Lev.swapAE D)).map (GlobalTheory.StdFrames.cpt Q) = M.map g := fun M => rfl
    have e3 : ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.Mem.R3.swapCast hF).symm).map g =
        (κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map f := rfl
    rw [e1, e2, hβ κ, Matrix.map_mul, Matrix.map_mul, e3, hK, Matrix.mul_one, ← Matrix.map_mul, h1,
      Matrix.map_one _ (map_zero g) (map_one g)]
  have e : (β⁻¹ * Formalism.IndefR.Lev.finE V (P.ψ κ) * β).val.map (GlobalTheory.StdFrames.cpt Q) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)).map (GlobalTheory.StdFrames.cpt Q) := by
    have hinv : (β⁻¹).val.map (GlobalTheory.StdFrames.cpt Q) * β.val.map (GlobalTheory.StdFrames.cpt Q) = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
    calc (β⁻¹ * Formalism.IndefR.Lev.finE V (P.ψ κ) * β).val.map (GlobalTheory.StdFrames.cpt Q)
        = (β⁻¹).val.map (GlobalTheory.StdFrames.cpt Q) * (Formalism.IndefR.Lev.finE V (P.ψ κ)).val.map (GlobalTheory.StdFrames.cpt Q) *
            β.val.map (GlobalTheory.StdFrames.cpt Q) := by
          rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]
      _ = 1 := by rw [hmain, Matrix.mul_one, hinv]
      _ = _ := (Matrix.map_one _ (map_zero _) (map_one _)).symm
  exact congrFun (congrFun e a) b

end GlobalTheory.FrameOffPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTameBlockCharacterTypePlaceNotOverL
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.TameTau

theorem tauTame : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : Formalism.L2.Host.CharFrame D) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (i : T.Tw) (j : ℕ) (b : Bool)
    (kv : Σ kk : Fin 2, D.nd.PlG kk), 1 ≤ j → j ≤ D.R.m → NX.pG D kv ∉ placesOver D.host.E (T.l i) →
    TauTameT D T i j b kv := by
  intro _ D cf b0 b1 Sx T Sp i j b kv _ _ hl
  have hg := D.host.g_prime kv.1
  have hover := D.naut.plGw_over kv.1 kv.2
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_residue_char_of_tame_char_prime_residue_field (E := D.host.E) (Ω := D.nd.Om) (NX.pG D kv) (D.host.g kv.1) hg
    (GlobalTheory.Proof.EigenvalueCoprimeConjugation.normV_plGw D kv.1 kv.2) (by simpa [placesOver] using hover) (T.twistBaseCoefficientRing_isAdic i) (T.chi1 i j b)
    (T.twistCharacterFamily_continuous i j b) (fun A hA σ hσ => T.twistCharacterFamily_tame i j b kv.1 _ hover hl A hA σ hσ)
  refine ⟨(Units.map (baseCoeffToFractionRing D T i).toMonoidHom).comp τ, fun x u hu => ?_⟩
  rw [MonoidHom.comp_apply, Units.coe_map, hτ x u hu]
  rfl

end GlobalTheory.TameTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIrreducibleBaseChangeWeightTensorDualRepOfEmbeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIrreducible_baseChange_weightTensorDualRepOfEmbeddings : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → ∀ (K' : Type) [Field K'] [Algebra K K'],
      (Formalism.IndefR.NX.bcRep (K' := K') (GlobalTheory.AlgWtF.wtRepF emb lam)).IsIrreducible := by
  first | exact @GlobalTheory.AlgWtBC.isIrreducible_bcRep_wtRepF | exact GlobalTheory.AlgWtBC.isIrreducible_bcRep_wtRepF | (intros; apply GlobalTheory.AlgWtBC.isIrreducible_bcRep_wtRepF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfRationalUnitaryAdelicMulStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPointOf_rational_unitary_adelic_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (γ : UF E n) (g : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), IsPtOf hc g p → IsPtOf hc (ratAd F γ * g) (((γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) := by
  first | exact @GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd | exact GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd | (intros; apply GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCoefficientCompatibilityStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_coefficient_compatibility : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff T.Q.l) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La), LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) c' (fun g => (lev g, (LinearMap.id : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))) := by
  first | exact @GlobalTheory.LevelActAnyField.actLev_of_levIs | exact GlobalTheory.LevelActAnyField.actLev_of_levIs | (intros; apply GlobalTheory.LevelActAnyField.actLev_of_levIs <;> assumption)
end

