module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.TjcosetsLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentConjLeviEqBlockUpperTwistedSylvester
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc.LeviBlockConjugation

theorem blk_val {E : Type} [Field E] [NumberField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X).val = Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
  have hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
    exact (m.1.isUnit.map Matrix.detMonoidHom).mul (m.2.isUnit.map Matrix.detMonoidHom)
  unfold blk
  simp only [dif_pos hU, IsUnit.unit_spec]

theorem conj_blk (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w 1 X)⁻¹ * blk h w m 0 * blk h w 1 X = blk h w m (GlobalTheory.LeviDesc.adL m.1 m.2.val X) := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  ext : 1
  simp only [Units.val_mul, blk_val, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  congr 1
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.fromBlocks_inj, true_and, and_true]
  simp only [adL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_sub, ← Matrix.mul_assoc]
  rw [show m.1.val * (m.1⁻¹ : GL (Fin a) _).val = 1 from by simp]
  simp [Matrix.one_mul, add_sub_cancel]

end GlobalTheory.LeviDesc.LeviBlockConjugation
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtFnOfOfNotMem
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.Discrepancy

namespace GlobalTheory.FieldPair

section SlopeTestRemainingChoices

variable {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) {y : X} (hy : y ∈ U)


include hU in
theorem unitAt_fnOf_of_not_mem {s : Γ(X, U)} (hs : s ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal) :
    UnitAt y (fnOf U (gen_mem hy) s) := by
  letI := X.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hy⟩
  exact ⟨_, IsLocalization.map_units (X.presheaf.stalk y)
    (⟨s, hs⟩ : (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl), algebraMap_germ hy s⟩


include hU in
theorem regAt_exists_fraction {f : X.functionField} (hf : RegAt y f) :
    ∃ c s : Γ(X, U), s ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧
      f * fnOf U (gen_mem hy) s = fnOf U (gen_mem hy) c := by
  letI := X.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨⟨c, s⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl a
  refine ⟨c, s, s.2, ?_⟩
  have e' := congrArg (algebraMap _ X.functionField) e
  rw [map_mul] at e'
  rw [← algebraMap_germ hy, ← algebraMap_germ hy]
  exact e'

end SlopeTestRemainingChoices

theorem isUnit_iff_inv_mem {K : Type} [Field K] {R : ValuationSubring K} (u : R) :
    IsUnit u ↔ (u : K) ≠ 0 ∧ (u : K)⁻¹ ∈ R := by
  constructor
  · rintro ⟨v, rfl⟩
    have h : ((v : R) : K) * ((v⁻¹ : Rˣ) : R) = 1 := by
      rw [← R.coe_mul, Units.mul_inv]; rfl
    exact ⟨left_ne_zero_of_mul_eq_one h, (inv_eq_of_mul_eq_one_right h) ▸ (v⁻¹ : Rˣ).1.2⟩
  · rintro ⟨h0, hi⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem isPrimeOf_placeEquiv {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) (x : X) :
    (placeEquiv p E).IsPrimeOf (locRing x) ↔ ∃ z, z ⤳ x ∧ E.IsAt z := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have ord0 : ∀ {b : X.functionField}, b ≠ 0 → b ∈ E.ring → b⁻¹ ∈ E.ring →
      (placeEquiv p E).ord b = 0 := fun {b} h0 h1 h2 => by
    have a1 := ((placeEquiv p E).ord_nonneg_iff h0).2 h1
    have a2 := ((placeEquiv p E).ord_nonneg_iff (inv_ne_zero h0)).2 h2
    rw [Place.ord_inv] at a2
    omega
  constructor
  · rintro ⟨hC, hP⟩
    have hT : E.Through x := (contains_placeEquiv E x).1 hC
    let φ : Γ(X, U) →+* E.ring :=
      (fnOf U (gen_mem hx)).codRestrict E.ring fun a => hT _ (regAt_fnOf hx _ a)
    let P : PrimeSpectrum Γ(X, U) := ⟨(IsLocalRing.maximalIdeal E.ring).comap φ, inferInstance⟩
    have memP (s : Γ(X, U)) : s ∉ P.asIdeal ↔
        (fnOf U (gen_mem hx) s ≠ 0 ∧ (fnOf U (gen_mem hx) s)⁻¹ ∈ E.ring) := by
      change φ s ∉ IsLocalRing.maximalIdeal E.ring ↔ _
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
      exact isUnit_iff_inv_mem (φ s)
    have hPQ : P ≤ hU.primeIdealOf ⟨x, hx⟩ := fun s hs => by_contra fun hs' =>
      have h := unitAt_fnOf_of_not_mem hU hx hs'
      (memP s).2 ⟨h.ne_zero, hT _ h.inv.regAt⟩ hs
    have hz : hU.fromSpec P ∈ U := by
      have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
      rwa [hU.range_fromSpec] at this
    let z : U := ⟨hU.fromSpec P, hz⟩
    have hP' : hU.primeIdealOf z = P :=
      hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
    have hzx : (z : X) ⤳ x := by
      have h := ((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨x, hx⟩)).mp hPQ).map
        hU.fromSpec.continuous
      rwa [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h
    clear_value z
    refine ⟨z, hzx, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
    · obtain ⟨a, ha, b, hb, hb0, hord, e⟩ := hP f hf
      obtain ⟨b', t, ht, e2⟩ := regAt_exists_fraction hU hx (mem_locRing.1 hb)
      have hut := unitAt_fnOf_of_not_mem hU hx ht
      have htP : t ∉ P.asIdeal := (memP t).2 ⟨hut.ne_zero, hT _ hut.inv.regAt⟩
      have hb'0 : fnOf U (gen_mem hx) b' ≠ 0 := e2 ▸ mul_ne_zero hb0 hut.ne_zero
      have ht0 : (placeEquiv p E).ord (fnOf U (gen_mem hx) t) = 0 :=
        ord0 hut.ne_zero (hT _ hut.regAt) (hT _ hut.inv.regAt)
      have hob' : (placeEquiv p E).ord (fnOf U (gen_mem hx) b') = 0 := by
        rw [← e2, (placeEquiv p E).ord_mul hb0 hut.ne_zero, hord, ht0, add_zero]
      have hb'i : (fnOf U (gen_mem hx) b')⁻¹ ∈ E.ring :=
        ((placeEquiv p E).ord_nonneg_iff (inv_ne_zero hb'0)).1
          (by rw [Place.ord_inv, hob', neg_zero])
      have hb'P : b' ∉ P.asIdeal := (memP b').2 ⟨hb'0, hb'i⟩
      have hub' := unitAt_fnOf_of_not_mem hU z.2 (s := b') (by rw [hP']; exact hb'P)
      have hut' := unitAt_fnOf_of_not_mem hU z.2 (s := t) (by rw [hP']; exact htP)
      have hbz : UnitAt (z : X) b := by
        have eb : b = fnOf U (gen_mem hx) b' * (fnOf U (gen_mem hx) t)⁻¹ := by
          rw [← e2, mul_inv_cancel_right₀ hut.ne_zero]
        rw [eb]
        exact hub'.mul hut'.inv
      have haz : RegAt (z : X) a := regAt_of_specializes hzx (mem_locRing.1 ha)
      have ef : f = a * b⁻¹ := by rw [← e, mul_inv_cancel_right₀ hb0]
      rw [ef]
      exact haz.mul hbz.inv.regAt
    · obtain ⟨c, s, hs, e⟩ := regAt_exists_fraction hU z.2 hf
      have hs' : s ∉ P.asIdeal := by rw [← hP']; exact hs
      obtain ⟨hs0, hsi⟩ := (memP s).1 hs'
      have ef : f = fnOf U (gen_mem hx) c * (fnOf U (gen_mem hx) s)⁻¹ := by
        rw [← e, mul_inv_cancel_right₀ hs0]
      rw [ef]
      exact mul_mem (hT _ (regAt_fnOf hx _ c)) hsi
  · rintro ⟨z, hzx, hz⟩
    refine ⟨(contains_placeEquiv E x).2 (hz.through hzx), fun f hf => ?_⟩
    have hzU : z ∈ U := hzx.mem_open U.isOpen hx
    obtain ⟨c, s, hs, e⟩ := regAt_exists_fraction hU hzU ((hz f).1 hf)
    have hu := unitAt_fnOf_of_not_mem hU hzU hs
    exact ⟨_, mem_locRing.2 (regAt_fnOf hx _ c), _, mem_locRing.2 (regAt_fnOf hx _ s), hu.ne_zero,
      ord0 hu.ne_zero ((hz _).2 hu.regAt) ((hz _).2 hu.inv.regAt), e⟩

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCommutingEqMulNormOneTorus
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapTorus

theorem mul_of_comm_gen {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (u : B.A)
    (hu : Algebra.adjoin K.E {u} = ⊤) (f : B.A → B.A) (hadd : ∀ y z, f (y + z) = f y + f z)
    (hsmul : ∀ (c : K.E) y, f (c • y) = c • f y) (hcomm : ∀ y, f (u * y) = u * f y) :
    ∀ y, f y = f 1 * y := by
  have key : ∀ s ∈ Algebra.adjoin K.E {u}, ∀ y, f (s * y) = s * f y := by
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hcomm
    | algebraMap c => intro y; rw [← Algebra.smul_def, hsmul, Algebra.smul_def]
    | add x y _ _ hx hy => intro z; rw [add_mul, hadd, hx, hy, add_mul]
    | mul x y _ _ hx hy => intro z; rw [mul_assoc, hx, hy, mul_assoc]
  intro y
  have := key y (hu ▸ Algebra.mem_top) 1
  rw [mul_one] at this
  rw [this, mul_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem stdH_unitary (w : Pl E) {n : ℕ} (h : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (hh : cT (cj w) h * 1 * h = 1) (v v' : Fin n → w.adicCompletion E) :
    stdH w (h *ᵥ v) (h *ᵥ v') = stdH w v v' := by
  have e1 : ∀ y y' : Fin n → w.adicCompletion E, stdH w y y' = y ⬝ᵥ (fun k => cj w (y' k)) := fun _ _ => rfl
  have hmap : (fun k => cj w ((h *ᵥ v') k)) = (h.map (cj w)) *ᵥ (fun k => cj w (v' k)) := by
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum]
  have ht : hᵀ * h.map (cj w) = 1 := by
    have := congrArg Matrix.transpose hh
    simpa [cT, Matrix.transpose_mul] using this
  rw [e1, e1, hmap, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ht,
    Matrix.one_mulVec]

theorem stdH_single (w : Pl E) {n : ℕ} (v : Fin n → w.adicCompletion E) (i : Fin n) :
    stdH w v (Pi.single i 1) = v i := by
  simp [stdH, Pi.single_apply, apply_ite (cj w)]

theorem torusOf_mem_of_mem_UL_commute : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (Q : (w.adicCompletion E)[X]) (u x : B.A) (n : ℕ) (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), Fits w e B Q u → IsModelMap w e B u x γ ψ → ∀ h : GLw n w, h ∈ UL n w → h * γ = γ * h → torusOf w B ψ h ∈ B.T ∧ ∀ y, ψ ((torusOf w B ψ h : B.A) * y) = h.val *ᵥ ψ y := by
  intro E _ _ _ w hw K e B Q u x n γ ψ hfit hmod h hU hc
  obtain ⟨hsm, hu, hst⟩ := hmod
  have conj : ∀ g : GLw n w, g * γ = γ * g → ∀ y, ψ.symm (g.val *ᵥ ψ y) = ψ.symm (g.val *ᵥ ψ 1) * y := by
    intro g hg
    apply mul_of_comm_gen B u hfit.1 (fun y => ψ.symm (g.val *ᵥ ψ y))
    · intro y z; simp [map_add (f := _), Matrix.mulVec_add]
    · intro c y
      apply ψ.injective
      simp only [hsm, ψ.apply_symm_apply, Matrix.mulVec_smul]
    · intro y
      apply ψ.injective
      simp only [hu, ψ.apply_symm_apply, Matrix.mulVec_mulVec]
      rw [← Units.val_mul, ← Units.val_mul, hg]
  have hc' : h⁻¹ * γ = γ * h⁻¹ := (Commute.inv_left (show Commute h γ from hc)).eq
  set a := ψ.symm (h.val *ᵥ ψ 1) with ha_def
  set b := ψ.symm ((h⁻¹ : GLw n w).val *ᵥ ψ 1) with hb_def
  have hab : a * b = 1 := by
    rw [← conj h hc b, hb_def, ψ.apply_symm_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec, ψ.symm_apply_apply]
  let t : B.Aˣ := ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
  have hspec : ∀ y, ψ ((t : B.A) * y) = h.val *ᵥ ψ y := by
    intro y
    show ψ (a * y) = _
    rw [← conj h hc y, ψ.apply_symm_apply]
  have htor : torusOf w B ψ h = t := torusOf_spec w B ψ h t hspec
  rw [htor]
  refine ⟨?_, hspec⟩

  have hUJ : cT (cj w) h.val * 1 * h.val = 1 := by
    have : h ∈ UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      unfold UL at hU; rwa [if_neg hw] at hU
    exact this
  have hinv : ∀ y z, B.herm x ((t : B.A) * y) ((t : B.A) * z) = B.herm x y z := by
    intro y z
    apply e.injective
    rw [← hst, ← hst, hspec, hspec, stdH_unitary w h.val hUJ]
  have hzero : ∀ y z, B.herm x (((t : B.A) * B.σ (t : B.A) - 1) * y) z = 0 := by
    intro y z
    have h1 : B.herm x (((t : B.A) * B.σ (t : B.A) - 1) * y) z =
        B.herm x ((t : B.A) * y) ((t : B.A) * z) - B.herm x y z := by
      unfold GlobalTheory.UnitLemma.InvAlg.herm
      rw [← map_sub]
      congr 1
      rw [map_mul]; ring
    rw [h1, hinv, sub_self]
  have hnd : ∀ m : B.A, (∀ z, B.herm x m z = 0) → m = 0 := by
    intro m hm
    apply ψ.injective
    rw [map_zero]
    funext i
    have := congrArg e (hm (ψ.symm (Pi.single i 1)))
    rw [← hst, ψ.apply_symm_apply, stdH_single, map_zero] at this
    simpa using this
  have := hnd _ (hzero 1)
  rw [mul_one, sub_eq_zero] at this
  exact this

end GlobalTheory.KapTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingKernelEqOneAddLowRankOfUnitary
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

noncomputable section

open Matrix

namespace GlobalTheory.PlaneSU

open Formalism.UG

theorem cT_cT_invol {R : Type} [CommRing R] (c : R →+* R) (hc : ∀ x, c (c x) = x) {m p : Type}
    (P : Matrix m p R) : cT c (cT c P) = P := by
  ext i j; simp [cT, hc]

theorem eq_emb_of_fix {R : Type} [CommRing R] (c : R →+* R) (hc : ∀ x, c (c x) = x) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) R) (hJ : IsUnit J.det) (A : Matrix (Fin M) (Fin 2) R)
    (B : Matrix (Fin 2) (Fin M) R) (H : Matrix (Fin 2) (Fin 2) R) (hBA : B * A = 1)
    (h1 : cT c A * J = H * B) (h2 : J * A = cT c B * H) (G : Matrix (Fin M) (Fin M) R)
    (hG : cT c G * J * G = J) (hN : G * (1 - A * B) = 1 - A * B) :
    G = emb A B (B * G * A) ∧ cT c (B * G * A) * H * (B * G * A) = H := by
  set N := 1 - A * B with hNdef
  have hBN : B * N = 0 := by
    rw [hNdef, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hBA, Matrix.one_mul, sub_self]
  have hcN : cT c N = 1 - cT c B * cT c A := by
    rw [hNdef, cT_sub, cT_one, cT_mul]
  have hNJ : cT c N * J = J - cT c B * H * B := by
    rw [hcN, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have hNJA : cT c N * J * A = 0 := by
    rw [hNJ, Matrix.sub_mul, h2, Matrix.mul_assoc, hBA, Matrix.mul_one, sub_self]
  have hNJN : cT c N * J * N = J * N := by
    rw [hNJ, Matrix.sub_mul, Matrix.mul_assoc (cT c B * H), hBN, Matrix.mul_zero, sub_zero]
  have hAJA : cT c A * J * A = H := by
    rw [h1, Matrix.mul_assoc, hBA, Matrix.mul_one]
  have hAJN : cT c A * J * N = 0 := by
    rw [h1, Matrix.mul_assoc, hBN, Matrix.mul_zero]
  set W := N * G * A with hWdef
  have hcW : cT c W = cT c A * cT c G * cT c N := by
    rw [hWdef, cT_mul, cT_mul, Matrix.mul_assoc]
  have hWJA : cT c W * J * A = 0 := by
    rw [hcW, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT c N), hNJA, Matrix.mul_zero]
  have hWJN : cT c W * J * N = 0 := by
    have e1 : cT c W * J * N = cT c A * cT c G * (cT c N * J * N) := by
      rw [hcW]; simp only [Matrix.mul_assoc]
    have e2 : cT c G * (J * N) = J * N := by
      calc cT c G * (J * N) = cT c G * (J * (G * N)) := by rw [hN]
        _ = (cT c G * J * G) * N := by simp only [Matrix.mul_assoc]
        _ = J * N := by rw [hG]
    rw [e1, hNJN, Matrix.mul_assoc, e2, ← Matrix.mul_assoc, hAJN]
  have hsplit : A * B + N = 1 := by rw [hNdef]; abel
  have hWJ : cT c W * J = 0 := by
    calc cT c W * J = cT c W * J * (A * B + N) := by rw [hsplit, Matrix.mul_one]
      _ = cT c W * J * A * B + cT c W * J * N := by
          rw [Matrix.mul_add]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hWJA, hWJN, Matrix.zero_mul, add_zero]
  have hcW0 : cT c W = 0 := by
    calc cT c W = cT c W * J * J⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv J hJ, Matrix.mul_one]
      _ = 0 := by rw [hWJ, Matrix.zero_mul]
  have hW0 : W = 0 := by
    rw [← cT_cT_invol c hc W, hcW0]; ext i j; simp [cT]
  set X := B * G * A with hXdef
  have hGA : G * A = A * X := by
    calc G * A = (A * B + N) * G * A := by rw [hsplit, Matrix.one_mul]
      _ = A * X + W := by rw [hXdef, hWdef]; simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = A * X := by rw [hW0, add_zero]
  refine ⟨?_, ?_⟩
  · calc G = G * (A * B + N) := by rw [hsplit, Matrix.mul_one]
      _ = G * A * B + G * N := by rw [Matrix.mul_add, Matrix.mul_assoc]
      _ = A * X * B + N := by rw [hGA, hN]
      _ = emb A B X := by
          rw [emb, hNdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]; abel
  · calc cT c X * H * X = cT c X * (cT c A * J * A) * X := by rw [hAJA]
      _ = cT c (A * X) * J * (A * X) := by rw [cT_mul c A X]; simp only [Matrix.mul_assoc]
      _ = cT c (G * A) * J * (G * A) := by rw [hGA]
      _ = cT c A * (cT c G * J * G) * A := by rw [cT_mul c G A]; simp only [Matrix.mul_assoc]
      _ = H := by rw [hG, hAJA]

end GlobalTheory.PlaneSU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLatticeEqIffInvMulIntegral
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitLat

theorem mulVec_int_iff {K : UQ} {n : ℕ} (P : Matrix (Fin n) (Fin n) K.E) :
    (∀ u : Fin n → K.E, (∀ i, u i ∈ (algebraMap K.O K.E).range) →
      ∀ i, (P *ᵥ u) i ∈ (algebraMap K.O K.E).range) ↔
    ∀ i j, P i j ∈ (algebraMap K.O K.E).range := by
  constructor
  · intro h i j
    have := h (Pi.single j 1) (fun k => by
      by_cases hk : k = j
      · subst hk; simpa using Subring.one_mem _
      · simpa [hk] using Subring.zero_mem _) i
    simpa [Matrix.mulVec_single] using this
  · intro h u hu i
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (h i j) (hu j)

theorem unitLat_eq_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ q q' : UL n w, unitLat e B ψ q = unitLat e B ψ q' ↔ q⁻¹ * q' ∈ KL n w := by
  intro E _ _ _ _ w _ K e _ hint n B ψ q q'
  let R := (algebraMap K.O K.E).range
  let M : GLw n w → Matrix (Fin n) (Fin n) K.E := fun g => (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm
  have hMmul : ∀ g h : GLw n w, M (g * h) = M g * M h := fun g h => by
    simp only [M, Units.val_mul]
    exact Matrix.map_mul (f := (e.symm : w.adicCompletion E →+* K.E))
  have hM1 : M 1 = 1 := by
    simp only [M, Units.val_one]
    exact Matrix.map_one (f := e.symm) (map_zero _) (map_one _)
  have hent : ∀ g : GLw n w, (∀ i j, M g i j ∈ R) ↔ ∀ i j, (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j ∈ Ov E w := by
    intro g
    refine forall_congr' fun i => forall_congr' fun j => ?_
    show e.symm _ ∈ R ↔ _
    rw [hint, RingEquiv.apply_symm_apply]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm
  have hmem : ∀ g : UL n w, ∀ y, y ∈ unitLat e B ψ g ↔ ∀ i, (M ((g : GLw n w)⁻¹) *ᵥ ψ y) i ∈ R :=
    fun g y => Iff.rfl

  have hlat : unitLat e B ψ q = unitLat e B ψ q' ↔
      ∀ v : Fin n → K.E, ((∀ i, (M ((q : GLw n w)⁻¹) *ᵥ v) i ∈ R) ↔ ∀ i, (M ((q' : GLw n w)⁻¹) *ᵥ v) i ∈ R) := by
    rw [SetLike.ext_iff]
    constructor
    · intro h v
      have := h (ψ.symm v)
      rwa [hmem, hmem, LinearEquiv.apply_symm_apply] at this
    · intro h y
      rw [hmem, hmem]
      exact h (ψ y)

  have half : ∀ a b : GLw n w,
      (∀ v : Fin n → K.E, (∀ i, (M b⁻¹ *ᵥ v) i ∈ R) → ∀ i, (M a⁻¹ *ᵥ v) i ∈ R) ↔
      ∀ i j, M (a⁻¹ * b) i j ∈ R := by
    intro a b
    rw [← mulVec_int_iff]
    constructor
    · intro h u hu
      have h1 := h (M b *ᵥ u) (by
        rw [Matrix.mulVec_mulVec, ← hMmul, inv_mul_cancel, hM1, Matrix.one_mulVec]; exact hu)
      rwa [Matrix.mulVec_mulVec, ← hMmul] at h1
    · intro h v hv
      have h1 := h _ hv
      rwa [Matrix.mulVec_mulVec, ← hMmul, mul_assoc, mul_inv_cancel, mul_one] at h1
  have hKL : q⁻¹ * q' ∈ KL n w ↔
      ((q : GLw n w)⁻¹ * q') ∈ Formalism.UG.GLint (Fin n) (Ov E w) := by
    rw [KL, Subgroup.mem_subgroupOf]
    rfl
  rw [hKL, Formalism.UG.P.tjcosets_mem_K_iff, ← hent, ← hent, hlat]
  have hinv : ((q : GLw n w)⁻¹ * q')⁻¹ = (q' : GLw n w)⁻¹ * q := by group
  rw [hinv, ← half, ← half]
  constructor
  · intro h
    exact ⟨fun v hv => (h v).2 hv, fun v hv => (h v).1 hv⟩
  · intro h v
    exact ⟨h.2 v, h.1 v⟩

end GlobalTheory.InertUnitLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerBumpFiniteFactorPropertiesStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerBumpFiniteFactor_properties : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ), (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n → psiFin (GlobalTheory.Whittaker.superDiag u) = 1) → bumpFin (E := E) (n := n) 1 = 1 ∧ (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), ∀ g, bumpFin (u * g) = psiFin (GlobalTheory.Whittaker.superDiag u) * bumpFin g) ∧ (∀ k ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n, ∀ g, bumpFin (g * k) = bumpFin g) ∧ ∀ g, bumpFin g ≠ 0 → ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n := by
  first | exact @GlobalTheory.WhitBump.FinBump.bumpFin_props | exact GlobalTheory.WhitBump.FinBump.bumpFin_props | (intros; apply GlobalTheory.WhitBump.FinBump.bumpFin_props <;> assumption)
end

