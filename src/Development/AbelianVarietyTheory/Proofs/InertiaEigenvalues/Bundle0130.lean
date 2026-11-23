module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0116
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0120

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefficientFieldOfCharZero
section
open IsLocalRing

namespace GlobalTheory.CohenRegular

section Field
open Polynomial

theorem exists_coefficientField_of_charZero (S : Type) [CommRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    [CharZero (ResidueField S)] :
    ∃ Λ : Subring S, IsField Λ ∧ ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S := by
  let T : Set (Subring S) := {Λ | ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0}
  have hbot : (⊥ : Subring S) ∈ T := by
    intro x hx hm
    obtain ⟨n, rfl⟩ := Subring.mem_bot.1 hx
    rw [← residue_eq_zero_iff, map_intCast, Int.cast_eq_zero] at hm
    simp [hm]
  obtain ⟨Λ, -, hΛ⟩ := zorn_le_nonempty₀ T (fun c hc hch y hy => by
    refine ⟨sSup c, fun x hx => ?_, fun z hz => le_sSup hz⟩
    obtain ⟨K, hK, hxK⟩ := (Subring.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).1 hx
    exact hc hK x hxK) ⊥ hbot
  have hT : ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0 := hΛ.prop
  have hF : IsField Λ := by
    refine ⟨exists_pair_ne _, mul_comm, fun {x} hx => ?_⟩
    have hu : IsUnit (x : S) := by
      by_contra h
      exact hx (Subtype.ext (hT _ x.2 h))
    let Λ' : Subring S :=
      { carrier := {s | ∃ n : ℕ, (x : S) ^ n * s ∈ Λ}
        one_mem' := ⟨0, by simp⟩
        zero_mem' := ⟨0, by simp⟩
        mul_mem' := by
          rintro a b ⟨n, hn⟩ ⟨m, hm⟩
          exact ⟨n + m, by convert Λ.mul_mem hn hm using 1; ring⟩
        add_mem' := by
          rintro a b ⟨n, hn⟩ ⟨m, hm⟩
          exact ⟨n + m, by
            convert Λ.add_mem (Λ.mul_mem (Λ.pow_mem x.2 m) hn) (Λ.mul_mem (Λ.pow_mem x.2 n) hm) using 1; ring⟩
        neg_mem' := by
          rintro a ⟨n, hn⟩
          exact ⟨n, by convert Λ.neg_mem hn using 1; ring⟩ }
    have h' : Λ' ∈ T := by
      rintro s ⟨n, hn⟩ hm
      exact (hu.pow n).mul_right_eq_zero.1 (hT _ hn (Ideal.mul_mem_left _ _ hm))
    have hle : Λ' ≤ Λ := hΛ.le_of_ge h' fun s hs => ⟨0, by simpa using hs⟩
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    exact ⟨⟨y, hle ⟨1, by rw [pow_one, hy]; exact Λ.one_mem⟩⟩, Subtype.ext hy⟩
  refine ⟨Λ, hF, fun s => ?_⟩
  letI := hF.toField
  have key : ∀ a : S, (∀ f : Λ[X], aeval a f ∈ maximalIdeal S → aeval a f = 0) → a ∈ Λ := fun a ha => by
    have h' : (aeval (R := Λ) a).toRingHom.range ∈ T := by
      rintro _ ⟨f, rfl⟩ hm
      exact ha f hm
    exact hΛ.le_of_ge h' (fun y hy => ⟨C ⟨y, hy⟩, by simp; rfl⟩) ⟨X, by simp⟩
  have hres : ∀ (a : S) (f : Λ[X]), residue S (aeval a f) = aeval (residue S a) f := fun a f =>
    (aeval_algHom_apply (IsScalarTower.toAlgHom Λ S (ResidueField S)) a f).symm
  by_cases hs : IsAlgebraic Λ (residue S s)
  · have hi := hs.isIntegral
    haveI : CharZero Λ := RingHom.charZero (algebraMap Λ (ResidueField S))
    have hsep : (minpoly Λ (residue S s)).Separable := (minpoly.irreducible hi).separable
    obtain ⟨a, ha, has⟩ := HenselianRing.is_henselian (I := maximalIdeal S)
      ((minpoly Λ (residue S s)).map (algebraMap Λ S)) ((minpoly.monic hi).map _) s
      (by rw [eval_map_algebraMap, ← residue_eq_zero_iff, hres, minpoly.aeval])
      (by
        rw [derivative_map, eval_map_algebraMap]
        have := hsep.aeval_derivative_ne_zero (minpoly.aeval Λ (residue S s))
        rw [← hres] at this
        exact (isUnit_iff_ne_zero (G₀ := ResidueField S)).2 this)
    have e : residue S a = residue S s := by rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact has
    refine ⟨a, key a fun f hf => ?_, by rw [← neg_sub]; exact neg_mem has⟩
    rw [← residue_eq_zero_iff, hres, e] at hf
    obtain ⟨q, rfl⟩ := minpoly.dvd _ _ hf
    rw [IsRoot.def, eval_map_algebraMap] at ha
    rw [map_mul, ha, zero_mul]
  · refine ⟨s, key s fun f hf => ?_, by simp⟩
    rw [← residue_eq_zero_iff, hres] at hf
    by_contra h
    exact hs ⟨f, by rintro rfl; simp at h, hf⟩

end Field

open MvPowerSeries GlobalTheory.CohenStructure

end GlobalTheory.CohenRegular
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactPreimageNormCentralizerHermitian
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.NormSec

theorem normsec : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∀ M : Set (GL (Fin r) E), IsCompact M → ∃ S : Set (GL (Fin r) E), IsCompact S ∧ ∀ t : GL (Fin r) E, (t : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) E) → (∃ m ∈ M, (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) = (m : Matrix (Fin r) (Fin r) E)) → ∃ s ∈ S, (s : Matrix (Fin r) (Fin r) E) * A₀ = A₀ * (s : Matrix (Fin r) (Fin r) E) ∧ (s : Matrix (Fin r) (Fin r) E) * star (s : Matrix (Fin r) (Fin r) E) = (t : Matrix (Fin r) (Fin r) E) * star (t : Matrix (Fin r) (Fin r) E) := by
  intro F E _ _ _ _ hU r A₀ hA hsep M hM
  classical
  have hA' : star A₀ = A₀ := by rw [Matrix.star_eq_conjTranspose]; exact hA
  obtain ⟨f, hfA, hff, hffs, haniso⟩ := _root_.GlobalTheory.IsoIdem.isoIdem E r A₀ hA hsep
  have hcomm := _root_.GlobalTheory.CommSep.commute_of_commute_separable E r A₀ hsep
  have hstarC : ∀ m : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → star m * A₀ = A₀ * star m := by
    intro m hm
    have := congrArg star hm
    rw [star_mul, star_mul, hA'] at this
    exact this.symm
  set g := star f with hg
  set e : Matrix (Fin r) (Fin r) E := 1 - f - g with he
  have hes : star e = 1 - g - f := by rw [he, star_sub, star_sub, star_one, hg, star_star]
  let R := Subring.centralizer ({A₀} : Set (Matrix (Fin r) (Fin r) E))
  have memR : ∀ m : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → m ∈ R := by
    intro m hm
    rw [Subring.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    exact hm.symm
  have memR' : ∀ m ∈ R, m * A₀ = A₀ * m := by
    intro m hm
    exact ((Subring.mem_centralizer_iff.1 hm) A₀ rfl).symm
  letI : CommRing R := { (inferInstance : Ring R) with
    mul_comm := fun a b => Subtype.ext (hcomm a.1 b.1 (memR' _ a.2) (memR' _ b.2)) }
  let V : Submodule E (Matrix (Fin r) (Fin r) E) :=
    { carrier := {z | z * A₀ = A₀ * z ∧ z * e = z}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        exact ⟨by rw [add_mul, mul_add, ha1, hb1], by rw [add_mul, ha2, hb2]⟩
      zero_mem' := ⟨by simp, by simp⟩
      smul_mem' := by
        rintro c a ⟨ha1, ha2⟩
        exact ⟨by rw [Matrix.smul_mul, Matrix.mul_smul, ha1], by rw [Matrix.smul_mul, ha2]⟩ }
  have hV : ∀ z ∈ V, z * star z = 0 → z = 0 := by
    rintro z ⟨hz1, hz2⟩ h0
    have h := haniso z hz1
    rw [hz2] at h
    exact h h0
  let M₁ := (fun u : GL (Fin r) E => (u : Matrix (Fin r) (Fin r) E)) '' M
  let M₂ := (fun u : GL (Fin r) E => ((u⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) '' M
  have hM₁ : IsCompact M₁ := hM.image Units.continuous_val
  have hM₂ : IsCompact M₂ := hM.image Units.continuous_coe_inv
  let B₁ := (fun x => x * e) '' M₁
  let B₂ := (fun x => x * e) '' M₂
  have hB₁ : IsCompact B₁ := hM₁.image (continuous_mul_const e)
  have hB₂ : IsCompact B₂ := hM₂.image (continuous_mul_const e)
  have hT₁ := _root_.GlobalTheory.mul_star_anisotropic_proper F E r V hV B₁ hB₁
  have hT₂ := _root_.GlobalTheory.mul_star_anisotropic_proper F E r V hV B₂ hB₂
  let P₁ := (fun p : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E => p.1 + p.2 * f + g) ''
    ({z | z ∈ V ∧ z * star z ∈ B₁} ×ˢ M₁)
  let P₂ := (fun p : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E => p.1 + p.2 * f + g) ''
    ({z | z ∈ V ∧ z * star z ∈ B₂} ×ˢ M₂)
  have hP₁ : IsCompact P₁ := (hT₁.prod hM₁).image (by fun_prop)
  have hP₂ : IsCompact P₂ := (hT₂.prod hM₂).image (by fun_prop)
  refine ⟨{s | (s : Matrix (Fin r) (Fin r) E) ∈ P₁ ∧ ((s⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) ∈ P₂}, ?_, ?_⟩
  · have := Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hP₁.prod (hP₂.image MulOpposite.continuous_op))
    convert this using 1
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod]
    rw [MulOpposite.op_injective.mem_set_image]
  rintro t ht ⟨m, hmM, hm⟩
  set T : Matrix (Fin r) (Fin r) E := (t : Matrix (Fin r) (Fin r) E) with hT
  set Ti : Matrix (Fin r) (Fin r) E := ((t⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hTi
  set mm : Matrix (Fin r) (Fin r) E := (m : Matrix (Fin r) (Fin r) E) with hmm
  set mi : Matrix (Fin r) (Fin r) E := ((m⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hmi
  have cTi : Ti * A₀ = A₀ * Ti := Commute.units_inv_left (u := t) ht
  have cm : mm * A₀ = A₀ * mm := by
    rw [← hm, mul_assoc, hstarC _ ht, ← mul_assoc, ht, mul_assoc]
  have cmi : mi * A₀ = A₀ * mi := Commute.units_inv_left (u := m) cm
  let xT : R := ⟨T, memR _ ht⟩
  let xTp : R := ⟨star T, memR _ (hstarC _ ht)⟩
  let xTi : R := ⟨Ti, memR _ cTi⟩
  let xTip : R := ⟨star Ti, memR _ (hstarC _ cTi)⟩
  let xmi : R := ⟨mi, memR _ cmi⟩
  let xf : R := ⟨f, memR _ hfA⟩
  let xg : R := ⟨g, memR _ (hstarC _ hfA)⟩
  have hfR : xf * xf = xf := Subtype.ext hff
  have hgR : xg * xg = xg := Subtype.ext (by show star f * star f = star f; rw [← star_mul, hff])
  have hfgR : xf * xg = 0 := Subtype.ext hffs
  have hTiR : xT * xTi = 1 := Subtype.ext (Units.mul_inv t)
  have hTpiR : xTp * xTip = 1 := Subtype.ext (by
    show star T * star Ti = 1
    rw [← star_mul, hT, hTi, Units.inv_mul, star_one])
  have hmiR : xmi * (xT * xTp) = 1 := Subtype.ext (by
    show mi * (T * star T) = 1
    rw [hm, hmi, hmm, Units.inv_mul])
  have heR : (1 - xf - xg) * (1 - xf - xg) = 1 - xf - xg := by linear_combination hfR + hgR + 2 * hfgR
  have hefR : (1 - xf - xg) * xf = 0 := by linear_combination -hfR - hfgR
  have hegR : (1 - xf - xg) * xg = 0 := by linear_combination -hgR - hfgR
  let X₀ : R := xT * (1 - xf - xg) + xT * xTp * xf + xg
  let X₁ : R := xTi * (1 - xf - xg) + xmi * xf + xg
  have h01 : X₀ * X₁ = 1 := by
    linear_combination (1 - xf - xg) * (1 - xf - xg) * hTiR + heR + xT * xmi * hefR + xT * hegR +
      xT * xTp * xTi * hefR + xf * xf * hmiR + hfR + xT * xTp * hfgR + xTi * hegR + xmi * hfgR + hgR
  have h10 : X₁ * X₀ = 1 := by rw [mul_comm]; exact h01
  let s : GL (Fin r) E := ⟨X₀.1, X₁.1, congrArg Subtype.val h01, congrArg Subtype.val h10⟩
  have hX₀ : X₀.1 = T * e + mm * f + g := by
    show T * (1 - f - g) + T * star T * f + g = _
    rw [hm]
  have hX₁ : X₁.1 = Ti * e + mi * f + g := rfl
  refine ⟨s, ⟨?_, ?_⟩, ?_, ?_⟩
  · refine ⟨(T * e, mm), ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨m, hmM, rfl⟩⟩, hX₀.symm⟩
    · exact memR' _ (xT * (1 - xf - xg)).2
    · have : xT * (1 - xf - xg) * (1 - xf - xg) = xT * (1 - xf - xg) := by linear_combination xT * heR
      exact congrArg Subtype.val this
    · refine ⟨mm, ⟨m, hmM, rfl⟩, ?_⟩
      have : xT * xTp * (1 - xf - xg) = xT * (1 - xf - xg) * ((1 - xg - xf) * xTp) := by
        linear_combination (-(xT * xTp)) * heR
      have h2 := congrArg Subtype.val this
      show mm * e = T * e * star (T * e)
      rw [star_mul, hes, ← hm]
      exact h2
  · refine ⟨(Ti * e, mi), ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨m, hmM, rfl⟩⟩, hX₁.symm⟩
    · exact memR' _ (xTi * (1 - xf - xg)).2
    · have : xTi * (1 - xf - xg) * (1 - xf - xg) = xTi * (1 - xf - xg) := by linear_combination xTi * heR
      exact congrArg Subtype.val this
    · refine ⟨mi, ⟨m, hmM, rfl⟩, ?_⟩
      have hTT : xTi * xTip = xmi := by
        linear_combination (-(xTi * xTip)) * hmiR + xmi * xTp * xTip * hTiR + xmi * hTpiR
      have : xmi * (1 - xf - xg) = xTi * (1 - xf - xg) * ((1 - xg - xf) * xTip) := by
        linear_combination (-(xTi * xTip)) * heR - (1 - xf - xg) * hTT
      have h2 := congrArg Subtype.val this
      show mi * e = Ti * e * star (Ti * e)
      rw [star_mul, hes]
      exact h2
  · exact memR' _ X₀.2
  · have : X₀ * ((1 - xg - xf) * xTp + xg * (xT * xTp) + xf) = xT * xTp := by
      linear_combination xT * xTp * heR + xT ^ 2 * xTp * hegR + xT * hefR + xT * xTp ^ 2 * hefR +
        xT ^ 2 * xTp ^ 2 * hfgR + xT * xTp * hfR + xTp * hegR + xT * xTp * hgR + hfgR
    have h2 := congrArg Subtype.val this
    have hst : star X₀.1 = ((1 - xg - xf) * xTp + xg * (xT * xTp) + xf).1 := by
      show star (T * (1 - f - g) + T * star T * f + g) = (1 - g - f) * star T + g * (T * star T) + f
      rw [hg]
      simp only [star_add, star_mul, star_sub, star_one, star_star]
    show X₀.1 * star X₀.1 = T * star T
    rw [hst]
    exact h2

end GlobalTheory.NormSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConductorMulMemAdjoinOfSeparable
section
noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

theorem exists_conductor_mul_mem_adjoin : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsIntegral K.O B.g →
    ∃ c : K.O, c ≠ 0 ∧ ∀ u : B.A, IsIntegral K.O u →
      algebraMap K.O B.A c * u ∈ Algebra.adjoin K.O ({B.g} : Set B.A) := by
  intro K B hP hg
  classical
  obtain ⟨e, he⟩ := exists_basis_pow_of_separable K B hP
  have hint : ∀ x : B.A, IsIntegral K.O x →
      ∃ t : K.O, algebraMap K.O K.E t = Algebra.trace K.E B.A x := fun x hx =>
    IsIntegrallyClosed.isIntegral_iff.1
      (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral K.O K.E B.A x hx)
  have he_int : ∀ i, IsIntegral K.O (e i) := fun i => by rw [he]; exact hg.pow _
  have hG : ∀ i j, ∃ t : K.O, algebraMap K.O K.E t = Algebra.trace K.E B.A (e i * e j) :=
    fun i j => hint _ ((he_int i).mul (he_int j))
  choose t ht using hG
  let c : K.O := (Matrix.of t).det
  have hc : algebraMap K.O K.E c = (Algebra.traceMatrix K.E e).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [ht, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  have hgen : ∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f := by
    intro a
    refine ⟨∑ i : Fin (Module.finrank K.E B.A), monomial (i : ℕ) (e.repr a i), ?_⟩
    calc a = ∑ i, e.repr a i • e i := (e.sum_repr a).symm
      _ = _ := by simp [map_sum, aeval_monomial, he, Algebra.smul_def]
  have hdet : (Algebra.traceMatrix K.E e).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    have hwv : e.equivFun (∑ j, v j • e j) = v := by
      rw [← e.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
    have hti : ∀ i, Algebra.trace K.E B.A ((∑ j, v j • e j) * e i) = 0 := by
      intro i
      have := congrFun (Algebra.traceMatrix_of_basis_mulVec e (∑ j, v j • e j)) i
      rw [hwv, hv] at this
      exact this.symm
    have hw := GlobalTheory.UnitLemma.TraceNondeg.eq_zero_of_trace_mul_eq_zero K B hP hgen
      (∑ j, v j • e j) (fun y => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← e.sum_repr y, Finset.mul_sum, map_sum]
        simp [mul_smul_comm, hti])
    exact funext (Fintype.linearIndependent_iff.1 e.linearIndependent v hw)
  refine ⟨c, fun h0 => hdet (by rw [← hc, h0, map_zero]), fun u hu => ?_⟩
  obtain ⟨w, hw⟩ := GlobalTheory.DiscConductor.det_smul_eq_sum K.O K.E B.A _ e u
    (fun i j => ⟨_, ht i j⟩) (fun i => hint _ (hu.mul (he_int i)))
  have h1 : algebraMap K.O B.A c * u = ∑ j, w j • B.g ^ (j : ℕ) := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, ← Algebra.smul_def, hc, hw]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [algebraMap_smul, he]
  rw [h1]
  exact Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _) _

end GlobalTheory.UnitLemma
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsForallEqPowOfPowEqSelf
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.InertiaEigenvalues.FrobPow

open Polynomial

theorem eq_of_pow_eq_self_of_map_eq {O k : Type} [CommRing O] [IsDomain O] [Field k]
    (φ : O →+* k) (q : ℕ) (hq : (q : k) = 0) {y z : O} (hy : y ^ q = y) (hz : z ^ q = z)
    (h : φ y = φ z) : y = z := by
  have h1 := Commute.geom_sum₂_mul (Commute.all y z) q
  rw [hy, hz] at h1
  have h2 : ((∑ i ∈ Finset.range q, y ^ i * z ^ (q - 1 - i)) - 1) * (y - z) = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exfalso
    have h4 := congrArg φ h3
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_mul, map_pow, map_one, map_zero, h] at h4
    rw [geom_sum₂_self, hq, zero_mul, zero_sub, neg_eq_zero] at h4
    exact one_ne_zero h4
  · exact sub_eq_zero.1 h3

theorem exists_forall_eq_pow_of_pow_eq_self (l : ℕ) [Fact l.Prime] {O k : Type} [CommRing O]
    [IsDomain O] [Field k] [CharP k l] (φ : O →+* k) (τ : O →+* O)
    (hτ : ∀ x, φ x = 0 → φ (τ x) = 0) (n : ℕ) (hn : 0 < n) :
    ∃ a : ℕ, ∀ x : O, x ^ l ^ n = x → τ x = x ^ l ^ a := by
  classical
  have hl : l.Prime := Fact.out
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' hl.one_lt
  let S : Set O := {x | x ^ l ^ n = x}
  have hmon : ∀ (A : Type) [CommRing A] [Nontrivial A], (X ^ l ^ n - X : A[X]).Monic := by
    intro A _ _
    apply Monic.sub_of_left (monic_X_pow _)
    rw [degree_X, degree_X_pow]
    exact_mod_cast hq
  have hS : S.Finite := by
    refine (X ^ l ^ n - X : O[X]).roots.toFinset.finite_toSet.subset fun x hx => ?_
    have hx' : x ^ l ^ n = x := hx
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [mem_roots (hmon O).ne_zero]
    simp [hx']
  have hint : ∀ x ∈ S, IsIntegral ℤ x := by
    intro x hx
    have hx' : x ^ l ^ n = x := hx
    exact ⟨X ^ l ^ n - X, hmon ℤ, by simp [hx']⟩
  have hfin : Module.Finite ℤ (Algebra.adjoin ℤ S) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral hS hint
  let ι : Algebra.adjoin ℤ S →+* O := (Algebra.adjoin ℤ S).val.toRingHom
  obtain ⟨a, ha⟩ := GlobalTheory.exists_forall_eq_pow_of_ker_le l (Algebra.adjoin ℤ S) k (φ.comp ι)
    (φ.comp (τ.comp ι)) (fun x hx => hτ _ hx)
  refine ⟨a, fun x hx => ?_⟩
  have h1 : φ (τ x) = φ x ^ l ^ a := ha ⟨x, Algebra.subset_adjoin hx⟩
  refine eq_of_pow_eq_self_of_map_eq φ (l ^ n) ?_ ?_ ?_ ?_
  · rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow hn.ne']
  · rw [← map_pow, hx]
  · rw [← pow_mul, mul_comm, pow_mul, hx]
  · rw [h1, map_pow]

theorem exists_gal_eq_pow (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : 0 < n) (σ : GQ l) :
    ∃ a : ℕ, ∀ x : Om l, x ^ l ^ n = x → σ x = x ^ l ^ a := by
  have hl : l.Prime := Fact.out
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' hl.one_lt
  let v : Valuation (Om l) NNReal := (PadicAlgCl.valued l).v
  have hv : ∀ x : Om l, v (σ x) = v x := fun x =>
    NNReal.eq (spectralNorm_eq_of_equiv σ x).symm
  let O : ValuationSubring (Om l) := v.valuationSubring
  have hO : ∀ x : Om l, x ∈ O ↔ v x ≤ 1 := fun x => Iff.rfl
  have hm : ∀ x : O, IsLocalRing.residue O x = 0 ↔ v x < 1 := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact Valuation.mem_maximalIdeal_iff _ v
  have hch : CharP (IsLocalRing.ResidueField O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl).2 ?_
    rw [← map_natCast (IsLocalRing.residue O), hm]
    have : v (l : Om l) = 1 / (l : NNReal) := PadicAlgCl.valuation_p l
    rw [SubringClass.coe_natCast, this, one_div]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  let τ : O →+* O := (σ : Om l →+* Om l).restrict O O (fun x hx => by
    rw [hO] at hx ⊢
    exact (hv x).trans_le hx)
  have hτ : ∀ x : O, ((τ x : O) : Om l) = σ x := fun x => rfl
  obtain ⟨a, ha⟩ := exists_forall_eq_pow_of_pow_eq_self l (IsLocalRing.residue O) τ
    (fun x hx => by rw [hm] at hx ⊢; rw [hτ, hv]; exact hx) n hn
  refine ⟨a, fun x hx => ?_⟩
  have hxO : x ∈ O := by
    rw [hO]
    by_contra h
    have h' : 1 < v x := not_le.1 h
    have h2 : v x ^ 1 < v x ^ l ^ n := pow_lt_pow_right₀ h' hq
    rw [← map_pow, ← map_pow, hx, pow_one] at h2
    exact lt_irrefl _ h2
  have h3 := ha ⟨x, hxO⟩ (Subtype.ext (by simpa using hx))
  have h4 := congrArg (fun y : O => (y : Om l)) h3
  simpa [hτ] using h4

end GlobalTheory.InertiaEigenvalues.FrobPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonicBasePolynomialRootNearDecompositionStatement
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monic_base_polynomial_root_near_decomposition : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω), (∀ z : Ω, (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r) → ∀ f : Polynomial Ω, f.Monic → (∀ d ∈ Dec (F := E) A, ∀ i, d (f.coeff i) = f.coeff i) → ∀ β : Ω, f.eval β = 0 → ∀ r : Ω, r ≠ 0 → ∃ g : Polynomial E, g.Monic ∧ g.natDegree = f.natDegree ∧ ∃ β' : Ω, aeval β' g = 0 ∧ A.valuation (β' - β) < A.valuation r := by
  first | exact @GlobalTheory.WeilDeligne.exists_monic_base_root_near | exact GlobalTheory.WeilDeligne.exists_monic_base_root_near | (intros; apply GlobalTheory.WeilDeligne.exists_monic_base_root_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPlusElementEtaNormNegOne
section
noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial

theorem exists_plus_eta_norm_neg_one : ∀ (K : UQ) (B : InvAlg K) (f : B.A), IsIdempotentElem f → f ≠ 0 →
    (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) → B.σ f = f →
    ∃ y : B.A, B.Plus y ∧ y * (1 - f) = 1 - f ∧ K.eta (Algebra.norm K.E y) = -1 := by
  first
  | exact @_root_.GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm
  | exact _root_.GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm
  | (apply _root_.GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm ..)

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformizerCompatibleUnramifiedExtStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformizer_compatible_unramifiedExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∃ π : K.O, ∃ π' : K'.O, algebraMap K'.O K'.E π' = φ (algebraMap K.O K.E π) ∧ IsLocalRing.maximalIdeal K.O = Ideal.span {π} ∧ IsLocalRing.maximalIdeal K'.O = Ideal.span {π'} := by
  first | exact @GlobalTheory.UnitLemma.Unr.exists_unif | exact GlobalTheory.UnitLemma.Unr.exists_unif | (intros; apply GlobalTheory.UnitLemma.Unr.exists_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KrasnerLemmaDecompositionGroupStabilizerVersionStatement
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.krasnerLemma_decompositionGroup_stabilizer_version : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (β β' : Ω), (∀ d ∈ Dec (F := E) A, d β ≠ β → A.valuation (β' - β) < A.valuation (d β - β)) → ∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β := by
  first | exact @GlobalTheory.krasner_stabiliser | exact GlobalTheory.krasner_stabiliser | (intros; apply GlobalTheory.krasner_stabiliser <;> assumption)
end

