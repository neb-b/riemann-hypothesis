module

public import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.RingDataObjects
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaDetPoly
public import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.Bundle0003
public import Formalism.WachLatticeTwists.RamifiedBlockRings.Bundle0001

@[expose] public section

-- bundled from Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.CMemPolyT
section
open Finset Classical Polynomial

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

section
variable {O : Type} [CommRing O] {Xs : Type} (T : Subalgebra O (Xs → O))
  {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Group G] (r : G →* (Xs → Matrix d d O))

def polyT : Subalgebra O[X] (Xs → O[X]) where
  carrier := {f | ∀ k, (fun x => (f x).coeff k) ∈ T}
  mul_mem' := by
    intro f g hf hg k
    have h : (fun x => ((f * g) x).coeff k) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, (fun x => (f x).coeff p.1) * (fun x => (g x).coeff p.2) := by
      funext x; simp [Polynomial.coeff_mul, Finset.sum_apply]
    rw [h]
    exact T.sum_mem fun p _ => T.mul_mem (hf _) (hg _)
  add_mem' := by
    intro f g hf hg k
    have h : (fun x => ((f + g) x).coeff k) = (fun x => (f x).coeff k) + fun x => (g x).coeff k := by
      funext x; simp
    rw [h]
    exact T.add_mem (hf k) (hg k)
  algebraMap_mem' p := by
    intro k
    have h : (fun x => ((algebraMap O[X] (Xs → O[X]) p) x).coeff k) =
        algebraMap O (Xs → O) (p.coeff k) := by
      funext x; simp
    rw [h]
    exact T.algebraMap_mem _

theorem C_mem_polyT {c : Xs → O} (hc : c ∈ T) : (fun x => C (c x)) ∈ polyT T := by
  show ∀ k, (fun x => (C (c x)).coeff k) ∈ T
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hc
  · have h0 : (fun x => (C (c x)).coeff k) = 0 := by
      funext x
      simp [Polynomial.coeff_C, hk.ne']
    rw [h0]
    exact T.zero_mem

def rPoly : G →* (Xs → Matrix d d O[X]) where
  toFun g x := (r g x).map C
  map_one' := by funext x; simp
  map_mul' g h := by funext x; simp [Matrix.map_mul]

theorem lift_mem {a : Xs → Matrix d d O} (ha : a ∈ tSpan T r) :
    (fun x => (a x).map C) ∈ tSpan (polyT T) (rPoly r) := by
  obtain ⟨s, c, hc, rfl⟩ := ha
  refine ⟨s, fun g x => C (c g x), fun g => C_mem_polyT T (hc g), ?_⟩
  funext x
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [rPoly, Finset.sum_apply, Matrix.sum_apply, map_sum]

private theorem matrix_charpolyRev_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Matrix d d R) : (M.map f).charpolyRev = M.charpolyRev.map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply]
  · simp [Matrix.one_apply, h]

theorem detT (hG1 : ∀ (g : G) (k : ℕ), (fun x => (Matrix.charpolyRev (r g x)).coeff k) ∈ T)
    (M : Xs → Matrix d d O[X]) (hM : M ∈ tSpan (polyT T) (rPoly r)) (k : ℕ) :
    (fun x => (M x).det.coeff k) ∈ T := by
  have h1 : ∀ (g : G) (k : ℕ), FromT (polyT T) (fun x => (Matrix.charpolyRev (rPoly r g x)).coeff k) := by
    intro g k
    refine ⟨fun x => C ((Matrix.charpolyRev (r g x)).coeff k), C_mem_polyT T (hG1 g k), fun x => ?_⟩
    have hx : rPoly r g x = (r g x).map C := rfl
    dsimp only
    rw [hx, matrix_charpolyRev_map, Polynomial.coeff_map]
    rfl
  obtain ⟨u, hu, hux⟩ := det_poly_statement O[X] O[X] Xs G d (polyT T) (rPoly r) h1 1 (fun _ => M)
    (fun _ => hM) (Finsupp.single 0 (Fintype.card d))
  have key : ∀ x, u x = (M x).det := by
    intro x
    have hx := hux x
    dsimp only at hx
    rw [Fin.sum_univ_one, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, mul_comm,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow] at hx
    simpa using hx
  have hfun : (fun x => (M x).det.coeff k) = fun x => (u x).coeff k := by
    funext x
    rw [key x]
  rw [hfun]
  exact hu k

end

theorem blockPolyT : StatBlockPolyT := by
  intro O _ X T d _ _ G _ r hG1 e he a ha k
  have hE : (fun x => (e x).map C) ∈ spanSub (polyT T) (rPoly r) := lift_mem T r he
  have hA : (fun x => (a x).map C) ∈ spanSub (polyT T) (rPoly r) := lift_mem T r ha
  have hM : (fun x => (Polynomial.X : O[X]) • (e x).map C - (a x).map C + (1 - e x).map C) ∈
      spanSub (polyT T) (rPoly r) := by
    have hq : (fun x => (Polynomial.X : O[X]) • (e x).map C - (a x).map C + (1 - e x).map C) =
        algebraMap O[X] (X → Matrix d d O[X]) Polynomial.X * (fun x => (e x).map C) -
          (fun x => (a x).map C) + (1 - fun x => (e x).map C) := by
      funext x
      ext i j
      by_cases h : i = j
      · subst h
        simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_apply]
      · simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_apply, h]
    rw [hq]
    exact Subalgebra.add_mem _ (Subalgebra.sub_mem _
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hE) hA)
      (Subalgebra.sub_mem _ (Subalgebra.one_mem _) hE)
  exact detT T r hG1 _ hM k

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

-- bundled from Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.IdemFactor
section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem eCore {K : Type} [Field K] {S : Type} [Fintype S] [DecidableEq S] (A : Matrix S S K) (t : ℕ)
    (α : ℕ → K) (ht : 1 ≤ t)
    (hA : A.charpoly = ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (α i)))
    (hα : ∀ i j, i < t → j < t → α i = α j → i = j) :
    (let EA := ((List.range t).tail.map fun i => A - α i • (1 : Matrix S S K)).prod
     let δ := ∏ i ∈ Finset.Ioo 0 t, (α 0 - α i)
     EA * EA = δ • EA ∧ EA.rank = 1 ∧ A * EA = α 0 • EA ∧ δ ≠ 0) := by
  intro EA δ
  let q : Polynomial K := ∏ i ∈ Finset.Ioo 0 t, (Polynomial.X - Polynomial.C (α i))
  have hEA : EA = Polynomial.aeval A q := by
    show EA = Polynomial.aeval A (∏ i ∈ Finset.Ioo 0 t, (Polynomial.X - Polynomial.C (α i)))
    rw [← tailProd (fun i => Polynomial.X - Polynomial.C (α i)) t, map_list_prod, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
    simp [Algebra.algebraMap_eq_smul_one]
  have hp : A.charpoly = (Polynomial.X - Polynomial.C (α 0)) * q := by
    rw [hA, Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot (by omega)]
    congr 1
  have hδq : q.eval (α 0) = δ := by
    simp [q, δ, Polynomial.eval_prod]
  have hδ : δ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
    rw [Finset.mem_Ioo] at hi
    intro h
    have := hα 0 i (by omega) hi.2 (sub_eq_zero.mp h)
    omega
  have hCH : Polynomial.aeval A ((Polynomial.X - Polynomial.C (α 0)) * q) = 0 := by
    rw [← hp]; exact Matrix.aeval_self_charpoly A
  have hAE : A * EA = α 0 • EA := by
    have h1 := hCH
    rw [map_mul, ← hEA] at h1
    have h2 : Polynomial.aeval A (Polynomial.X - Polynomial.C (α 0)) = A - α 0 • 1 := by
      simp [Algebra.algebraMap_eq_smul_one]
    rw [h2, sub_mul, sub_eq_zero] at h1
    rw [h1]; simp
  have hsq : EA * EA = δ • EA := by
    obtain ⟨h, hh⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := α 0) (p := q)
    rw [hδq] at hh
    have h3 : q * q = Polynomial.C δ * q + h * ((Polynomial.X - Polynomial.C (α 0)) * q) := by
      have : q = Polynomial.C δ + (Polynomial.X - Polynomial.C (α 0)) * h := by rw [← hh]; ring
      calc q * q = (Polynomial.C δ + (Polynomial.X - Polynomial.C (α 0)) * h) * q := by rw [← this]
        _ = _ := by ring
    rw [hEA, ← map_mul, h3, map_add (f := _), map_mul, map_mul _ h, hCH, mul_zero, add_zero,
      Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  refine ⟨hsq, ?_, hAE, hδ⟩
  let φ : Module.End K (S → K) := Matrix.toLin' A
  have hφc : φ.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  apply le_antisymm
  · have h1 : LinearMap.range EA.mulVecLin ≤ φ.eigenspace (α 0) := by
      rintro _ ⟨v, rfl⟩
      rw [Module.End.mem_eigenspace_iff]
      show A.mulVec (EA.mulVec v) = α 0 • EA.mulVec v
      rw [Matrix.mulVec_mulVec, hAE, Matrix.smul_mulVec]
    have h2 : Polynomial.rootMultiplicity (α 0) φ.charpoly = 1 := by
      have hq0 : q ≠ 0 := fun h => hδ (by rw [← hδq, h]; simp)
      rw [hφc, hp, Polynomial.rootMultiplicity_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero _) hq0),
        Polynomial.rootMultiplicity_X_sub_C_self,
        Polynomial.rootMultiplicity_eq_zero (by rw [Polynomial.IsRoot, hδq]; exact hδ)]
    calc EA.rank = Module.finrank K (LinearMap.range EA.mulVecLin) := rfl
      _ ≤ Module.finrank K (φ.eigenspace (α 0)) := Submodule.finrank_mono h1
      _ ≤ 1 := h2 ▸ LinearMap.finrank_eigenspace_le φ (α 0)
  · have hroot : φ.charpoly.IsRoot (α 0) := by
      rw [hφc, hp, Polynomial.IsRoot, Polynomial.eval_mul]; simp
    obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly φ (α 0)).mpr hroot).exists_hasEigenvector
    have h1 := Module.End.aeval_apply_of_hasEigenvector (p := q) hv
    have h2 : Polynomial.aeval φ q = Matrix.toLin' EA := by
      rw [hEA]
      exact (Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix S S K ≃ₐ[K] _) A q)
    rw [h2, hδq] at h1
    by_contra hlt
    have h0 : EA.rank = 0 := by omega
    have h3 : LinearMap.range EA.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h0
    have h4 : EA.mulVecLin v ∈ LinearMap.range EA.mulVecLin := LinearMap.mem_range_self _ v
    rw [h3, Submodule.mem_bot] at h4
    have h5 : δ • v = 0 := by rw [← h1]; exact h4
    exact hv.2 ((smul_eq_zero.mp h5).resolve_left hδ)

theorem idem_factor {K : Type} [Field K] {d : Type} [Fintype d] [DecidableEq d] (e : Matrix d d K)
    (he : e * e = e) : ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (U : Matrix d S K)
      (W : Matrix S d K), U * W = e ∧ W * U = 1 := by
  obtain ⟨P, Q, dd, hdd, hPQ, hQP, rfl⟩ := idem_normal_form e he
  let J : Matrix d {a // dd a = 1} K := Matrix.of fun a i => if a = i.1 then 1 else 0
  have hJJ : J.transpose * J = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.of_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have h' : i.1 ≠ j.1 := fun e => hij (Subtype.ext e)
      simp [hij, h', Ne.symm h']
  have hJD : J * J.transpose = Matrix.diagonal dd := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.of_apply]
    by_cases ha : dd a = 1
    · rw [Finset.sum_eq_single ⟨a, ha⟩]
      · by_cases hab : a = b
        · subst hab; simp [ha]
        · simp [Matrix.diagonal_apply_ne _ hab, Ne.symm hab]
      · intro i _ hi
        have : a ≠ i.1 := fun e => hi (Subtype.ext e.symm)
        simp [this]
      · intro h; exact absurd (mem_univ _) h
    · have h0 : dd a = 0 := (hdd a).resolve_right ha
      rw [Finset.sum_eq_zero fun i _ => by
        have : a ≠ i.1 := fun e => ha (e ▸ i.2)
        simp [this]]
      by_cases hab : a = b
      · subst hab; simp [h0]
      · simp [Matrix.diagonal_apply_ne _ hab]
  refine ⟨{a // dd a = 1}, inferInstance, inferInstance, P * J, J.transpose * Q, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc J, hJD, ← Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQP, Matrix.one_mul, hJJ]

theorem eMat : StatEMat := by
  intro K _ d _ _ e x t α ht he hex hxe hpoly hα E
  obtain ⟨S, _, _, U, W, hUW, hWU⟩ := idem_factor e he
  let A : Matrix S S K := W * x * U
  have hx : x = U * A * W := by
    show x = U * (W * x * U) * W
    have : U * (W * x * U) * W = (U * W) * x * (U * W) := by simp only [Matrix.mul_assoc]
    rw [this, hUW, hex, hxe]
  have hsand : ∀ B B' : Matrix S S K, (U * B * W) * (U * B' * W) = U * (B * B') * W := by
    intro B B'
    have : (U * B * W) * (U * B' * W) = U * B * (W * U) * B' * W := by simp only [Matrix.mul_assoc]
    rw [this, hWU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have he1 : e = U * (1 : Matrix S S K) * W := by rw [Matrix.mul_one, hUW]
  have hf : ∀ i, x - α i • e = U * (A - α i • 1) * W := by
    intro i
    rw [Matrix.mul_sub, Matrix.sub_mul, ← hx, Matrix.mul_smul, Matrix.smul_mul, ← he1]
  have hlist : ∀ l : List ℕ, e * (l.map fun i => x - α i • e).prod =
      U * (l.map fun i => A - α i • (1 : Matrix S S K)).prod * W := by
    intro l
    induction l with
    | nil => simp [hUW]
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons]
      have h1 : e * ((x - α i • e) * (l.map fun i => x - α i • e).prod) =
          (x - α i • e) * (e * (l.map fun i => x - α i • e).prod) := by
        have h2 : e * (x - α i • e) = (x - α i • e) * e := by
          rw [mul_sub, sub_mul, hex, hxe, Matrix.mul_smul, Matrix.smul_mul]
        rw [← mul_assoc, h2, mul_assoc]
      rw [h1, ih, hf, hsand]
  have hchar : A.charpoly = ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (α i)) := by
    rw [← hpoly]
    unfold blockPoly Matrix.charpoly Matrix.charmatrix
    let C' : K →+* Polynomial K := Polynomial.C
    have hUW' : U.map C' * W.map C' = e.map C' := by rw [← Matrix.map_mul, hUW]
    have hWU' : W.map C' * U.map C' = 1 := by
      rw [← Matrix.map_mul, hWU, Matrix.map_one _ C'.map_zero C'.map_one]
    have hx' : x.map C' = U.map C' * A.map C' * W.map C' := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, ← hx]
    have h1 : (Polynomial.X : Polynomial K) • e.map C' - x.map C' + (1 - e).map C' =
        1 + U.map C' * (((Polynomial.X : Polynomial K) • 1 - A.map C' - 1) * W.map C') := by
      have h2 : (1 - e).map C' = 1 - e.map C' := by
        ext i j
        by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
      rw [h2, hx', ← hUW']
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_assoc]
      abel
    rw [h1, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hWU', Matrix.mul_one]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, C']
  obtain ⟨h1, h2, h3, h4⟩ := eCore A t α ht hchar hα
  set EA := ((List.range t).tail.map fun i => A - α i • (1 : Matrix S S K)).prod with hEAdef
  have hE : E = U * EA * W := hlist _
  have hEA : EA = W * E * U := by
    rw [hE]
    have : W * (U * EA * W) * U = (W * U) * EA * (W * U) := by simp only [Matrix.mul_assoc]
    rw [this, hWU, Matrix.one_mul, Matrix.mul_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, h4⟩
  · rw [hE, hsand, h1, Matrix.mul_smul, Matrix.smul_mul]
  · apply le_antisymm
    · rw [← h2, hE]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    · rw [← h2]
      calc EA.rank = (W * E * U).rank := congrArg Matrix.rank hEA
        _ ≤ E.rank := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · rw [hE, hx, hsand, h3, Matrix.mul_smul, Matrix.smul_mul]
  · rw [hE, he1, hsand, Matrix.one_mul]
  · rw [hE, he1, hsand, Matrix.mul_one]

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

-- bundled from Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.IdemKO
section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem idemKO : StatIdemKO := by
  intro O _ _ _ n _ _ e he hr
  classical
  set eK := e.map (algebraMap O (FractionRing O)) with heK
  have hidK : eK * eK = eK := by
    rw [heK, ← Matrix.map_mul, he]
  have hsub : (LinearMap.range (Matrix.toLin' eK)).subtype.comp (Matrix.toLin' eK).rangeRestrict =
      Matrix.toLin' eK := LinearMap.ext fun v => rfl
  have hid : (Matrix.toLin' eK).rangeRestrict.comp (LinearMap.range (Matrix.toLin' eK)).subtype =
      LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨v, w, rfl⟩
    apply Subtype.ext
    show Matrix.toLin' eK (Matrix.toLin' eK w) = Matrix.toLin' eK w
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hidK]
  have hfr : Module.finrank (FractionRing O) (LinearMap.range (Matrix.toLin' eK)) = 1 := by
    rw [← hr]
    rfl
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 1) (FractionRing O) (LinearMap.range (Matrix.toLin' eK))) :=
    ⟨Module.finBasisOfFinrankEq _ _ hfr⟩
  obtain ⟨U, W, hUW, hWU⟩ : ∃ (U : Matrix n (Fin 1) (FractionRing O))
      (W : Matrix (Fin 1) n (FractionRing O)), U * W = eK ∧ W * U = 1 :=
    ⟨LinearMap.toMatrix b (Pi.basisFun _ n) (LinearMap.range (Matrix.toLin' eK)).subtype,
      LinearMap.toMatrix (Pi.basisFun _ n) b (Matrix.toLin' eK).rangeRestrict,
      by rw [← LinearMap.toMatrix_comp, hsub, LinearMap.toMatrix_eq_toMatrix',
        LinearMap.toMatrix'_toLin'],
      by rw [← LinearMap.toMatrix_comp, hid, LinearMap.toMatrix_id]⟩
  have hfact : ∀ i j, eK i j = U i 0 * W 0 j := by
    intro i j
    rw [← hUW, Matrix.mul_apply, Fin.sum_univ_one]
  have hsum : ∑ i, W 0 i * U i 0 = 1 := by
    have h := congrFun (congrFun hWU 0) 0
    rwa [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have inj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O _
  have hmap : ∀ i j, algebraMap O (FractionRing O) (e i j) = eK i j := fun i j => rfl
  have htr : ∑ i, e i i = 1 := by
    apply inj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    simp only [hmap, hfact]
    rw [← hsum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  obtain ⟨i0, hi0⟩ : ∃ i0, IsUnit (e i0 i0) := by
    by_contra hcon
    push_neg at hcon
    have hmem : ∑ i, e i i ∈ IsLocalRing.maximalIdeal O :=
      Ideal.sum_mem _ fun i _ => (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 (hcon i))
    rw [htr] at hmem
    exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hmem) isUnit_one
  have hminor : ∀ i j k l, e i j * e k l = e i l * e k j := by
    intro i j k l
    apply inj
    simp only [map_mul, hmap, hfact]
    ring
  obtain ⟨c, hc⟩ := hi0
  have hfe : ∀ i j, e i j = e i i0 * (↑c⁻¹ * e i0 j) := by
    intro i j
    have h := hminor i j i0 i0
    rw [← hc] at h
    calc e i j = e i j * ↑c * ↑c⁻¹ := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h]; ring
  have hφu : ∑ j, ↑c⁻¹ * e i0 j * e j i0 = 1 := by
    have h := congrFun (congrFun he i0) i0
    rw [Matrix.mul_apply, ← hc] at h
    calc ∑ j, ↑c⁻¹ * e i0 j * e j i0 = ↑c⁻¹ * ∑ j, e i0 j * e j i0 := by
          rw [Finset.mul_sum]
          simp only [mul_assoc]
      _ = 1 := by rw [h, Units.inv_mul]
  let ψ : KO O →ₗ[O] (n → KO O) := LinearMap.pi fun i => e i i0 • LinearMap.id
  let χ : (n → KO O) →ₗ[O] KO O := ∑ j, (↑c⁻¹ * e i0 j) • LinearMap.proj j
  have hχψ : ∀ m, χ (ψ m) = m := by
    intro m
    simp only [χ, ψ, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, LinearMap.pi_apply, LinearMap.id_apply, smul_smul]
    rw [← Finset.sum_smul, hφu, one_smul]
  have hmat : matEnd O (KO O) n e = ψ.comp χ := by
    apply LinearMap.ext
    intro v
    funext i
    show ∑ j, e i j • v j = _
    simp only [χ, ψ, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.smul_apply,
      LinearMap.id_apply, LinearMap.sum_apply, LinearMap.proj_apply,
      Finset.smul_sum, smul_smul]
    exact Finset.sum_congr rfl fun j _ => by rw [hfe i j]
  have hinj : Function.Injective ψ := fun a b h => by rw [← hχψ a, ← hχψ b, h]
  have hχ : LinearMap.range χ = ⊤ := LinearMap.range_eq_top.2 fun m => ⟨ψ m, hχψ m⟩
  exact ⟨(LinearEquiv.ofEq _ _ (by rw [hmat, LinearMap.range_comp_of_range_eq_top ψ hχ])).trans
    (LinearEquiv.ofInjective ψ hinj).symm⟩

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

