module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PKpMem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem mem_intK_iff {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (a : K) :
    a ∈ GlobalTheory.LKLoc.intK p K ↔ ‖(a : PadicAlgCl p)‖ ≤ 1 := by
  show (algebraMap K (PadicAlgCl p) a) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p ↔ _
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff

theorem UpperTheory.Gal.W2.kpMem_of :
    UpperTheory.Gal.W2.KpMem := by
  intro p _ G g
  rw [GlobalTheory.HeckeP.inclG_mem_KHT_iff]
  unfold UpperTheory.Gal.W2.IntPt
  have hunit : (‖(g.1 : ℚ_[p])‖ ≤ 1 ∧ ‖((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1) ↔ ‖(g.1 : ℚ_[p])‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv]
    have hpos : 0 < ‖(g.1 : ℚ_[p])‖ := norm_pos_iff.2 g.1.ne_zero
    constructor
    · rintro ⟨h1, h2⟩
      exact le_antisymm h1 (by simpa using (inv_le_one₀ hpos).1 h2)
    · intro h
      rw [h]
      simp
  rw [hunit]
  apply and_congr_right'
  apply forall_congr'
  intro w
  unfold GlobalTheory.LKLoc.KintK
  rw [GlobalTheory.HeckeP.mem_range_map_subtype]
  simp only [mem_intK_iff]
  rw [← forall_and]
  apply forall_congr'
  intro i
  rw [← forall_and]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLocLat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private def colM {K : Type*} {n : ℕ} (b : Fin n → Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => b j i

private theorem colM_update {K : Type*} [Field K] {n : ℕ} (b : Fin n → Fin n → K) (i : Fin n)
    (y : Fin n → K) : (colM b).updateCol i y = colM (Function.update b i y) := by
  ext r c
  by_cases h : c = i
  · subst h; simp [colM, Matrix.updateCol_apply]
  · simp [colM, Matrix.updateCol_apply, h, Function.update_of_ne]

private theorem colM_mulVec {K : Type*} [Field K] {n : ℕ} (b : Fin n → Fin n → K)
    (c : Fin n → K) : colM b *ᵥ c = ∑ i, c i • b i := by
  ext r
  simp [colM, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

private theorem exists_frame {K : Type*} [Field K] (f : K → ℝ) (h0 : f 0 = 0)
    (hm : ∀ x y, f (x * y) = f x * f y) (hpos : ∀ x, x ≠ 0 → 0 < f x) (hnn : ∀ x, 0 ≤ f x)
    (ha : ∀ x y, f (x + y) ≤ max (f x) (f y)) {n : ℕ} (s : Finset (Fin n → K))
    (hs : Submodule.span K (s : Set (Fin n → K)) = ⊤) :
    ∃ b : Fin n → Fin n → K, (colM b).det ≠ 0 ∧ (∀ i, b i ∈ s) ∧
      ∀ y ∈ s, ∃ c : Fin n → K, (∀ i, f (c i) ≤ 1) ∧ colM b *ᵥ c = y := by
  classical
  have h1 : f 1 = 1 := by
    have h := hm 1 1
    have hp := hpos 1 one_ne_zero
    rw [_root_.one_mul] at h
    exact mul_left_cancel₀ hp.ne' (by rw [_root_.mul_one]; exact h.symm)
  obtain ⟨t, hts, hspan, hli⟩ := exists_linearIndependent K (s : Set (Fin n → K))
  have hfin : t.Finite := s.finite_toSet.subset hts
  haveI := hfin.fintype
  have htop : ⊤ ≤ Submodule.span K (Set.range ((↑) : t → Fin n → K)) := by
    rw [Subtype.range_coe, hspan, hs]
  have hcard : Fintype.card t = n := by
    have := Module.finrank_eq_card_basis (Module.Basis.mk hli htop)
    rw [Module.finrank_fin_fun] at this
    exact this.symm
  let e := Fintype.equivFinOfCardEq hcard
  let b0 : Fin n → Fin n → K := fun i => (e.symm i).1
  have hb0 : (colM b0).det ≠ 0 := by
    intro hd
    obtain ⟨v, hv, hMv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hd
    rw [colM_mulVec] at hMv
    have hli' : LinearIndependent K b0 := hli.comp e.symm e.symm.injective
    exact hv (funext (Fintype.linearIndependent_iff.mp hli' v hMv))
  let F : (Fin n → s) → ℝ := fun g => f (colM (fun i => (g i : Fin n → K))).det
  obtain ⟨g0, -, hg0⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n → s)) F
    ⟨fun i => ⟨b0 i, hts (e.symm i).2⟩, Finset.mem_univ _⟩
  let b : Fin n → Fin n → K := fun i => (g0 i : Fin n → K)
  have hle : F (fun i => ⟨b0 i, hts (e.symm i).2⟩) ≤ f (colM b).det := hg0 _ (Finset.mem_univ _)
  have hpos0 : 0 < f (colM b).det := lt_of_lt_of_le (hpos _ hb0) hle
  have hdet : (colM b).det ≠ 0 := by
    intro h
    rw [h, h0] at hpos0
    exact lt_irrefl _ hpos0
  refine ⟨b, hdet, fun i => (g0 i).2, ?_⟩
  intro y hy
  set d := (colM b).det with hd
  refine ⟨d⁻¹ • (colM b).cramer y, ?_, ?_⟩
  · intro i
    have hupd : Function.update b i y = fun j => ((Function.update g0 i ⟨y, hy⟩ j : s) : Fin n → K) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [b]
      · simp [b, Function.update_apply, hj]
    have hmax : f (colM (Function.update b i y)).det ≤ f d := by
      rw [hupd]
      exact hg0 _ (Finset.mem_univ _)
    have hinv : f d⁻¹ = (f d)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      rw [← hm, mul_inv_cancel₀ hdet, h1]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply, colM_update]
    rw [hm, hinv, inv_mul_le_iff₀ hpos0, _root_.mul_one]
    exact hmax
  · rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hdet, one_smul]

private theorem exists_gl {K : Type} [Field K] (f : K → ℝ) (h0 : f 0 = 0)
    (hm : ∀ x y, f (x * y) = f x * f y) (hpos : ∀ x, x ≠ 0 → 0 < f x) (hnn : ∀ x, 0 ≤ f x)
    (ha : ∀ x y, f (x + y) ≤ max (f x) (f y)) {n : ℕ} (s : Finset (Fin n → K))
    (hs : Submodule.span K (s : Set (Fin n → K)) = ⊤) :
    ∃ g : GL (Fin n) K, ∀ z : Fin n → K,
      (∀ i, f ((((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z) i) ≤ 1) ↔
        ∃ a : (Fin n → K) → K, (∀ y, f (a y) ≤ 1) ∧ z = ∑ y ∈ s, a y • y := by
  classical
  obtain ⟨b, hdet, hbs, hcoord⟩ := exists_frame f h0 hm hpos hnn ha s hs
  have hu : IsUnit (colM b) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  refine ⟨hu.unit, ?_⟩
  have hl : ((hu.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * colM b = 1 := by
    have h := Units.inv_mul hu.unit
    rwa [IsUnit.unit_spec] at h
  have hr : colM b * ((hu.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    have h := Units.mul_inv hu.unit
    rwa [IsUnit.unit_spec] at h
  have hsum : ∀ {α : Type} (t : Finset α) (u : α → K), (∀ i ∈ t, f (u i) ≤ 1) →
      f (∑ i ∈ t, u i) ≤ 1 := by
    intro α t u hu'
    exact Finset.sum_induction u (fun x => f x ≤ 1)
      (fun x y hx hy => (ha x y).trans (max_le hx hy)) (by rw [h0]; exact zero_le_one) hu'
  intro z
  constructor
  · intro hz
    set c := ((hu.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z with hc
    have hzc : z = colM b *ᵥ c := by
      rw [hc, Matrix.mulVec_mulVec, hr, Matrix.one_mulVec]
    refine ⟨fun y => ∑ i, if b i = y then c i else 0, ?_, ?_⟩
    · intro y
      apply hsum
      intro i _
      split_ifs
      · exact hz i
      · rw [h0]
        exact zero_le_one
    · rw [hzc, colM_mulVec]
      simp only [Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ite_smul, zero_smul]
      rw [Finset.sum_ite_eq, if_pos (hbs i)]
  · rintro ⟨a, ha1, rfl⟩ i
    choose! C hC1 hC2 using hcoord
    have hz : ∑ y ∈ s, a y • y = colM b *ᵥ ∑ y ∈ s, a y • C y := by
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [Matrix.mulVec_smul, hC2 y hy]
    rw [hz, Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply hsum
    intro y hy
    rw [hm]
    exact mul_le_one₀ (ha1 y) (hnn _) (hC1 y hy i)

theorem UpperTheory.Gal.W2.locLat_of :
    UpperTheory.Gal.W2.LocLat := by
  intro p _ G w s hs
  exact exists_gl (fun x : G.Fw w => ‖(x : PadicAlgCl p)‖) (by simp)
    (fun x y => by
      push_cast
      exact norm_mul _ _)
    (fun x hx => norm_pos_iff.mpr (by exact_mod_cast hx))
    (fun x => norm_nonneg _)
    (fun x y => by
      push_cast
      exact IsUltrametricDist.norm_add_le_max _ _) s hs
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PMemDual
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.memDual_of :
    UpperTheory.Gal.W2.TrDual → UpperTheory.Gal.W2.MemDual := by
  intro h p _ G
  choose d hd0 hd using fun w : Fin G.m => h p G w
  refine ⟨d, hd0, fun a => ?_⟩
  constructor
  · intro ha w i
    have key := (hd w (a w i)).1 (fun z0 hz0 => by
      have hz : IntL (Pi.single w (Pi.single i z0) : Loc G) := by
        intro w' j
        by_cases hw : w' = w
        · subst hw
          by_cases hj : j = i
          · subst hj
            simpa using hz0
          · simp [Pi.single_apply, hj]
        · simp [Pi.single_apply, hw]
      have hp := ha _ hz
      have he : pairL a (Pi.single w (Pi.single i z0) : Loc G) =
          Algebra.trace ℚ_[p] (G.Fw w) (a w i * z0) := by
        unfold pairL
        rw [Finset.sum_eq_single w]
        · simp
        · intro w' _ hw'
          simp [Pi.single_apply, hw']
        · simp
      rwa [he] at hp)
    simpa [mul_comm] using key
  · intro ha z hz
    unfold pairL
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro w _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro i _
    have hai : ‖((a w i * d w : G.Fw w) : PadicAlgCl p)‖ ≤ 1 := by
      simpa [mul_comm] using ha w i
    exact (hd w (a w i)).2 hai (z w i) (hz w i)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.POOnto
section
noncomputable section

open NumberField
open scoped TensorProduct Matrix Classical
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace UpperTheory.Gal.W2

private theorem tens_inj (p : ℕ) [Fact p.Prime] {O : Type} [Ring O] [Module.Free ℤ O] :
    Function.Injective (fun x : O => x ⊗ₜ[ℤ] (1 : ℤ_[p])) := by
  have hinj : Function.Injective (Algebra.linearMap ℤ ℤ_[p]) := by
    intro a b h
    exact RingHom.injective_int (algebraMap ℤ ℤ_[p]) h
  have h1 := Module.Flat.lTensor_preserves_injective_linearMap (M := O) (Algebra.linearMap ℤ ℤ_[p]) hinj
  intro x y hxy
  have h2 : x ⊗ₜ[ℤ] (1 : ℤ) = y ⊗ₜ[ℤ] (1 : ℤ) := h1 (by simpa using hxy)
  have h3 := congrArg (TensorProduct.rid ℤ O) h2
  simpa using h3

private theorem comm_of_split (p : ℕ) [Fact p.Prime] {O : Type} [Ring O] [Module.Free ℤ O] {R : Type} [CommRing R]
    {m : ℕ} (hm : m = 1) (f : (O ⊗[ℤ] ℤ_[p]) ≃+* Matrix (Fin m) (Fin m) R) (x y : O) : x * y = y * x := by
  subst hm
  apply tens_inj p
  have hc : ∀ A B : Matrix (Fin 1) (Fin 1) R, A * B = B * A := by
    intro A B
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Matrix.mul_apply, mul_comm]
  have := hc (f (x ⊗ₜ[ℤ] (1 : ℤ_[p]))) (f (y ⊗ₜ[ℤ] (1 : ℤ_[p])))
  rw [← map_mul, ← map_mul] at this
  have h2 := f.injective this
  simpa using h2

private theorem a_inj {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] [Algebra (𝓞 F) O] [Nontrivial O]
    [Module.Free ℤ O] : Function.Injective (algebraMap (𝓞 F) O) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra h0
  have hI : RingHom.ker (algebraMap (𝓞 F) O) ≠ ⊥ := fun h => h0 (by
    have h1 : c ∈ RingHom.ker (algebraMap (𝓞 F) O) := hc
    rw [h] at h1
    simpa using h1)
  have hN := Ideal.absNorm_mem (RingHom.ker (algebraMap (𝓞 F) O))
  have hN0 : Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) O)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hI
  rw [RingHom.mem_ker, map_natCast] at hN
  have h1 : (Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) O)) : ℤ) • (1 : O) = 0 := by
    rw [zsmul_one]
    exact_mod_cast hN
  rcases smul_eq_zero.mp h1 with h | h
  · exact hN0 (by exact_mod_cast h)
  · exact one_ne_zero h

private theorem a_onto {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] [Algebra (𝓞 F) O] [Nontrivial O]
    [Module.Free ℤ O] [Module.Finite ℤ O] (hcomm : ∀ x y : O, x * y = y * x)
    (hc : ∀ x : O, ∃ c : 𝓞 F, ∃ e : ℤ, e ≠ 0 ∧ e • x = algebraMap (𝓞 F) O c) :
    Function.Surjective (algebraMap (𝓞 F) O) := by
  intro x
  obtain ⟨c, e, he, hx⟩ := hc x
  letI : CommRing O := { (inferInstance : Ring O) with mul_comm := hcomm }
  obtain ⟨P, hP, hPx⟩ : IsIntegral ℤ x := IsIntegral.of_finite ℤ x
  have hQ : Polynomial.eval₂ (algebraMap ℤ O) (algebraMap ℤ O e * x) (P.scaleRoots e) = 0 := by
    rw [Polynomial.scaleRoots_eval₂_mul, hPx, mul_zero]
  have hex : algebraMap ℤ O e * x = algebraMap (𝓞 F) O c := by
    rw [← hx]; simp [zsmul_eq_mul]
  have hQ2 : Polynomial.eval₂ (algebraMap ℤ (𝓞 F)) c (P.scaleRoots e) = 0 := by
    apply a_inj (O := O)
    rw [map_zero, Polynomial.hom_eval₂, ← hex, ← hQ]
    congr 1
    exact RingHom.ext_int _ _
  have hQ3 : Polynomial.eval₂ (algebraMap ℤ F) (c : F) (P.scaleRoots e) = 0 := by
    have := congrArg (algebraMap (𝓞 F) F) hQ2
    rw [map_zero, Polynomial.hom_eval₂] at this
    rw [← this]
    congr 1
  have heF : (algebraMap ℤ F e) ≠ 0 := by simpa using he
  have hcF : (c : F) = algebraMap ℤ F e * ((c : F) / algebraMap ℤ F e) := by field_simp
  rw [hcF, Polynomial.scaleRoots_eval₂_mul] at hQ3
  have hint : IsIntegral ℤ ((c : F) / algebraMap ℤ F e) :=
    ⟨P, hP, (mul_eq_zero.mp hQ3).resolve_left (pow_ne_zero _ heF)⟩
  obtain ⟨c', hc'⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 hint
  refine ⟨c', ?_⟩
  have hcc : c = e • c' := by
    apply RingOfIntegers.ext
    rw [hcF, ← hc']
    simp [zsmul_eq_mul]
  have h3 : e • (algebraMap (𝓞 F) O c' - x) = 0 := by
    rw [smul_sub, hx, hcc, zsmul_eq_mul, zsmul_eq_mul]
    simp
  rcases smul_eq_zero.mp h3 with h | h
  · exact absurd h he
  · exact sub_eq_zero.mp h

theorem oOnto_of : OOnto := by
  intro p _ D hm
  haveI := D.freeO
  haveI := D.finO
  have hd : 0 < Module.finrank ℚ D.F := Module.finrank_pos
  haveI : Nontrivial D.O := by
    apply Module.nontrivial_of_finrank_pos (R := ℤ)
    rw [D.rankO, hm]
    simpa using hd
  obtain ⟨f⟩ := D.splitP
  have hcomm : ∀ x y : D.O, x * y = y * x := comm_of_split p hm f.toRingEquiv
  exact a_onto hcomm fun x => D.central x (hcomm x)

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPLatOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem plat_core {V : Type} [AddCommGroup V] [Module ℚ V] (p : ℕ) (hp : p ≠ 0) (M : AddSubgroup V)
    (s : Finset V) (k : ℕ) (hs : Submodule.span ℚ (s : Set V) = ⊤)
    (hsat : ∀ (m : ℕ) x, m.Coprime p → m • x ∈ M → x ∈ M)
    (h1 : ∀ x ∈ s, p ^ k • x ∈ M)
    (h2 : ∀ x ∈ M, ∃ m : ℕ, m.Coprime p ∧ (m * p ^ k) • x ∈ AddSubgroup.closure (s : Set V)) :
    ∃ t : Finset V, Submodule.span ℚ (t : Set V) = ⊤ ∧
      ∀ w, w ∈ M ↔ ∃ m : ℕ, m.Coprime p ∧ m • w ∈ AddSubgroup.closure (t : Set V) := by
  have hpk : ((p : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp)
  set q : ℚ := ((p : ℚ) ^ k)⁻¹ with hq
  let f : V →ₗ[ℤ] V := (LinearMap.lsmul ℚ V q).toAddMonoidHom.toIntLinearMap
  have hf : ∀ x, f x = q • x := fun x => rfl
  set W : Submodule ℤ V := Submodule.span ℤ (f '' (s : Set V)) with hW
  have hWfg : W.FG := Submodule.fg_span ((s.finite_toSet).image f)
  haveI : IsNoetherian ℤ W := isNoetherian_of_fg_of_noetherian W hWfg
  have hNfg : (AddSubgroup.toIntSubmodule M ⊓ W).FG :=
    Submodule.FG.of_le_of_isNoetherian inf_le_right
  obtain ⟨t, ht⟩ := hNfg
  have hcl : ∀ y, y ∈ AddSubgroup.closure (t : Set V) ↔ y ∈ M ∧ y ∈ W := by
    intro y
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup, ht,
      Submodule.mem_inf]
    rfl
  have hsW : ∀ y ∈ AddSubgroup.closure (s : Set V), q • y ∈ W := by
    intro y hy
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup] at hy
    have hy' : f y ∈ (Submodule.span ℤ (s : Set V)).map f := Submodule.mem_map_of_mem hy
    rw [Submodule.map_span] at hy'
    rw [← hf]
    exact hy'
  refine ⟨t, ?_, fun w => ⟨fun hw => ?_, fun ⟨m, hm, hmw⟩ => hsat m w hm ((hcl _).1 hmw).1⟩⟩
  · rw [eq_top_iff, ← hs, Submodule.span_le]
    intro x hx
    have hx1 : p ^ k • x ∈ M := h1 x hx
    have e : p ^ k • x = q • ((p ^ k * p ^ k) • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
      congr 1
      push_cast
      rw [hq, ← _root_.mul_assoc, inv_mul_cancel₀ hpk, _root_.one_mul]
    have hx2 : p ^ k • x ∈ W := by
      rw [e]
      exact hsW _ (AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure hx) _)
    have hmem : p ^ k • x ∈ Submodule.span ℚ (t : Set V) :=
      (AddSubgroup.closure_le (K := (Submodule.span ℚ (t : Set V)).toAddSubgroup)).2
        Submodule.subset_span ((hcl _).2 ⟨hx1, hx2⟩)
    have e2 : x = q • (p ^ k • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
      push_cast
      rw [hq, inv_mul_cancel₀ hpk, one_smul]
    show x ∈ Submodule.span ℚ (t : Set V)
    rw [e2]
    exact Submodule.smul_mem _ q hmem
  · obtain ⟨m, hm, hmem⟩ := h2 w hw
    refine ⟨m, hm, (hcl _).2 ⟨M.nsmul_mem hw m, ?_⟩⟩
    have e : m • w = q • ((m * p ^ k) • w) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
      congr 1
      push_cast
      rw [hq, _root_.mul_comm (m : ℚ), ← _root_.mul_assoc, inv_mul_cancel₀ hpk, _root_.one_mul]
    rw [e]
    exact hsW _ hmem

theorem UpperTheory.Gal.W2.pLatOf_of :
    UpperTheory.Gal.W2.PLatOf := by
  intro p _ D M s k hs hO hsat h1 h2
  exact ⟨hO, plat_core p (Fact.out : p.Prime).ne_zero M s k hs hsat h1 h2⟩
end

