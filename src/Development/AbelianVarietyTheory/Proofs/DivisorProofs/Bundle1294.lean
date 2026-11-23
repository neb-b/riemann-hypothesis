module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIsKroneckerCharOfDiscr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1245
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationNonnegIffSpanMultiplicationTranslates

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEliminationFormGeneralLinearFormsCone
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem exists_elim_form_of_field : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ) (I : Ideal (MvPolynomial (Fin N) F)) (g : MvPolynomial (Fin N) F), 1 ≤ D → I.IsPrime → (∀ a ∈ I, ∀ n : ℕ, homogeneousComponent n a ∈ I) → ringKrullDim (MvPolynomial (Fin N) F ⧸ I) = (D + 1 : ℕ) → g.IsHomogeneous d → g ∉ I → ∃ Q : MvPolynomial (Fin D × Fin N) F, Q ≠ 0 ∧ ∀ (K : Type) [Field K] [Algebra F K] (s : Fin D → Fin N → K) (y : Fin N → K), y ≠ 0 → (∀ a ∈ I, aeval y a = 0) → aeval y g = 0 → (∀ i, ∑ j, s i j * y j = 0) → aeval (fun p : Fin D × Fin N => s p.1 p.2) Q = 0 := by
  intro F _ _ D N d I g hD hI hhom hdim hg hgI
  obtain ⟨Q, hQ0, -, hQ⟩ := GlobalTheory.HSElim.exists_elim_form F D N d I g hD hI hhom hdim hg hgI
  refine ⟨Q, hQ0, ?_⟩
  intro K _ _ s y hy hyI hyg hlin
  classical
  let ey : Fin N → (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) := fun j => Sum.inr (Sum.inl j)
  let ez : Fin N → (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) := fun j => Sum.inr (Sum.inr j)
  let gens : Set (MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F) :=
    ((rename ey) '' (I : Set _) ∪ {rename ey g}) ∪
    (Set.range (fun i : Fin D => ∑ j, X (Sum.inl (i, j)) * X (ey j)) ∪ {∑ j, X (ez j) * X (ey j) - 1})
  let f := rename (Sum.inl : Fin D × Fin N → (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) Q
  have hclos : ∀ x : (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) → AlgebraicClosure F,
      (∀ p ∈ Ideal.span gens, aeval x p = 0) → aeval x f = 0 := by
    intro x hx
    have h' : ∀ p ∈ gens, aeval x p = 0 := fun p hp => hx p (Ideal.subset_span hp)
    have hz : ∑ j, x (ez j) * x (ey j) = 1 := by
      have := h' _ (Or.inr (Or.inr rfl))
      simpa [sub_eq_zero] using this
    have hy0 : (fun j => x (ey j)) ≠ 0 := by
      intro h0
      have : ∑ j, x (ez j) * x (ey j) = 0 := by
        simp [show ∀ j, x (ey j) = 0 from fun j => congrFun h0 j]
      rw [hz] at this
      exact one_ne_zero this
    simp only [f, aeval_rename]
    exact hQ (AlgebraicClosure F) (fun i j => x (Sum.inl (i, j))) (fun j => x (ey j)) hy0
      (fun a ha => by
        have := h' _ (Or.inl (Or.inl ⟨a, ha, rfl⟩))
        simpa [aeval_rename, Function.comp_def] using this)
      (by
        have := h' _ (Or.inl (Or.inr rfl))
        simpa [aeval_rename, Function.comp_def] using this)
      (fun i => by
        have := h' _ (Or.inr (Or.inl ⟨i, rfl⟩))
        simpa using this)
  obtain ⟨j0, hj0⟩ : ∃ j0, y j0 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hy (funext hcon)
  let z : Fin N → K := fun j => if j = j0 then (y j0)⁻¹ else 0
  let x0 : (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) → K := Sum.elim (fun p => s p.1 p.2) (Sum.elim y z)
  have hx0 : ∀ p ∈ Ideal.span gens, aeval x0 p = 0 := by
    intro p hp
    have hle : Ideal.span gens ≤ RingHom.ker (aeval x0 : MvPolynomial _ F →ₐ[F] K) := by
      rw [Ideal.span_le]
      rintro q ((⟨a, ha, rfl⟩ | rfl) | (⟨i, rfl⟩ | rfl))
      · simpa [aeval_rename, Function.comp_def, x0, ey] using hyI a ha
      · simpa [aeval_rename, Function.comp_def, x0, ey] using hyg
      · simpa [x0, ey] using hlin i
      · simp [x0, ey, ez, z, hj0]
    exact hle hp
  have := _root_.GlobalTheory.vanish_transfer_of_algClosure F ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) (Ideal.span gens) f hclos K x0 hx0
  simpa [f, aeval_rename, Function.comp_def, x0] using this

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionPrincipalTriplesTensorLatti
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.TenPair

theorem spMap_comp_ringHom {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]
  rfl

theorem mapRingHom_comp {K K' K'' : Type} [Field K] [Field K'] [Field K''] (f : K →+* K') (g : K' →+* K'') :
    (RingOfIntegers.mapRingHom g).comp (RingOfIntegers.mapRingHom f) = RingOfIntegers.mapRingHom (g.comp f) :=
  RingHom.ext fun _ => rfl

theorem exists_isTen_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (A B : PAT H (Sp (𝓞 K))) (r s : ℕ),
    ρ ^ 2 = -(H.d : 𝓞 K) → HasType H A.t.act ρ r 0 → HasType H B.t.act ρ s 0 →
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (j : K →+* K') (ω : 𝓞 K') (C : Ell H (𝓞 K') ω)
      (A' B' : PAT H (Sp (𝓞 K'))) (_ : SABMap A'.t A.t (spMap (RingOfIntegers.mapRingHom j)))
      (_ : SABMap B'.t B.t (spMap (RingOfIntegers.mapRingHom j))) (DA DB : Datum H)
      (hA : DA.La → DA.La → OK H) (hB : DB.La → DB.La → OK H),
      DA.p + DA.q = r ∧ DB.p + DB.q = s ∧ Nonempty (IsTen C DA hA A') ∧ Nonempty (IsTen C DB hB B') := by
  intro E _ _ _ H K _ _ ρ A B r s hρ hA hB
  have hU : ThetaUnifAV := GlobalTheory.thetaUnifAV_all
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hE : HomExtDvr := GlobalTheory.homExtension_semiAbelian_dvr_unconditional
  have hC : CMCurve := GlobalTheory.cmCurve_closed
  have hPB : Out.PolBaseChangeSt := hL.polBaseChange
  haveI : NeZero H.d := ⟨H.d_prime.ne_zero⟩
  obtain ⟨χ, hχ⟩ := GlobalTheory.exists_isKroneckerChar (d := H.d) H.d_prime.ne_zero (Or.inr (by have := H.d_mod; omega))
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hρ₀ : (σ (ρ : K)) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (σ.comp (algebraMap (𝓞 K) K)) hρ
    simpa using this
  obtain ⟨M, _, ω, C, x, hω, hP, -, -⟩ := GlobalTheory.CM.EllExists.exists_ell hC hU hL hE E H χ hχ _ hρ₀
  obtain ⟨k, _, j, i, hj, hi⟩ := PureDeg.exists_compositum K σ M
  obtain ⟨A', mA', -⟩ := PAT.exists_pullback E H _ _ (spMap (RingOfIntegers.mapRingHom j)) A
  obtain ⟨C', φ', hC'⟩ := exists_ellMap hPB E H _ ω C _ (RingOfIntegers.mapRingHom i)
  have e : 2 * RingOfIntegers.mapRingHom i ω - 1 = RingOfIntegers.mapRingHom j ρ := by
    apply RingOfIntegers.ext
    apply Subtype.ext
    have h1 : (((RingOfIntegers.mapRingHom j ρ : 𝓞 k) : k) : ℂ) = σ ρ := hj _
    have h2 : (((RingOfIntegers.mapRingHom i ω : 𝓞 k) : k) : ℂ) = (ω : M) := hi _
    rw [h1, ← hω, ← h2]
    rfl
  have hA' : HasType H A'.t.act (2 * RingOfIntegers.mapRingHom i ω - 1) r 0 := by
    rw [e]
    exact (hasType_baseChange E H _ _ _ A.t A'.t mA' ρ r 0).1 (PureDeg.mapRingHom_injective j) hA
  have hP' : C'.IsPrincipalAt ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) := by
    refine (EllComp.ellMap_comp E H _ ω C _ _ C' _ φ' hC').2.1 _ ?_
    convert hP using 1
    ext a
    exact hi _
  obtain ⟨k₁, _, hk, ω₁, C₁, φ₁, A₁, mA₁, DA, -, ha, hC₁, hDA, -, -, ⟨tA⟩⟩ :=
    GlobalTheory.CM.Recog.exists_isTen_of_hasType hU hL hE E H k _ C' A' r hP' hA'
  let j₁ : K →+* k₁ := (IntermediateField.inclusion hk).toRingHom.comp j
  obtain ⟨B₁, mB₁, -⟩ := PAT.exists_pullback E H _ _ (spMap (RingOfIntegers.mapRingHom j₁)) B
  have e₁ : 2 * ω₁ - 1 = RingOfIntegers.mapRingHom j₁ ρ := by
    have h3 := congrArg (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom) e
    simp only [map_sub, map_mul, map_ofNat, map_one, hC₁.1] at h3
    rw [h3]
    rfl
  have hB₁ : HasType H B₁.t.act (2 * ω₁ - 1) s 0 := by
    rw [e₁]
    exact (hasType_baseChange E H _ _ _ B.t B₁.t mB₁ ρ s 0).1 (PureDeg.mapRingHom_injective j₁) hB
  have hP₁ : C₁.IsPrincipalAt ((algebraMap k₁ ℂ).comp (algebraMap (𝓞 k₁) k₁)) := by
    refine (EllComp.ellMap_comp E H _ _ C' _ _ C₁ _ φ₁ hC₁).2.1 _ ?_
    convert hP' using 1
    ext a
    rfl
  obtain ⟨k₂, _, hk', ω₂, C₂, φ₂, B₂, mB₂, DB, -, hb, hC₂, hDB, -, -, ⟨tB⟩⟩ :=
    GlobalTheory.CM.Recog.exists_isTen_of_hasType hU hL hE E H k₁ ω₁ C₁ B₁ s hP₁ hB₁
  obtain ⟨A₂, mA₂, -⟩ := PAT.exists_pullback E H _ _
    (spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk').toRingHom)) A₁
  obtain ⟨tA₂, -⟩ := isTen_baseChange E H _ ω₁ C₁ DA ha A₁ tA _ ω₂ C₂ _ φ₂ A₂ mA₂ hC₂
  let J : K →+* k₂ := (IntermediateField.inclusion hk').toRingHom.comp j₁
  obtain ⟨nA₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mA' mA₁
  obtain ⟨nA, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp nA₁ mA₂
  obtain ⟨nB, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mB₁ mB₂
  have eA : spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk').toRingHom) ≫
      (spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom) ≫
        spMap (RingOfIntegers.mapRingHom j)) = spMap (RingOfIntegers.mapRingHom J) := by
    rw [spMap_comp_ringHom, spMap_comp_ringHom, mapRingHom_comp, mapRingHom_comp]
  have eB : spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk').toRingHom) ≫
      spMap (RingOfIntegers.mapRingHom j₁) = spMap (RingOfIntegers.mapRingHom J) := by
    rw [spMap_comp_ringHom, mapRingHom_comp]
  exact ⟨k₂, inferInstance, inferInstance, J, ω₂, C₂, A₂, B₂, eA ▸ nA, eB ▸ nB, DA, DB, ha, hb, hDA, hDB,
    ⟨tA₂⟩, ⟨tB⟩⟩

end GlobalTheory.CM.TenPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataPrincipalCongruenceLevel
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.PrincData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem isIntegral_cc {x : E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (cc x) :=
  hx.map ((IsCMField.complexConj E : E →+* E).toIntAlgHom)

theorem herm_add_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem herm_add_right (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y + y') = herm G x y + herm G x y' := by
  simp only [herm, cc, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (x y : Fin r → E) :
    herm G (c • x) y = (c : E) * herm G x y := by
  simp only [herm, Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Algebra.smul_def, show algebraMap (𝓞 E) E c = (c : E) from rfl]; ring

theorem herm_smul_right (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (x y : Fin r → E) :
    herm G x (c • y) = cc (c : E) * herm G x y := by
  simp only [herm, Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Algebra.smul_def]
  simp only [cc, map_mul]
  ring

theorem exists_nat_herm_int (G : Matrix (Fin r) (Fin r) E) (L : Submodule (𝓞 E) (Fin r → E)) (hL : L.FG) :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ ((n : E) * herm G x y) := by
  classical
  obtain ⟨s, rfl⟩ := hL
  obtain ⟨y0, hy0, hy⟩ := exists_integral_multiples ℤ ℚ ((s ×ˢ s).image fun p => herm G p.1 p.2)
  have hgen : ∀ a ∈ s, ∀ b ∈ s, IsIntegral ℤ ((y0 : E) * herm G a b) := fun a ha b hb => by
    have h := hy _ (Finset.mem_image.2 ⟨(a, b), Finset.mem_product.2 ⟨ha, hb⟩, rfl⟩)
    rwa [zsmul_eq_mul] at h
  have hright : ∀ a ∈ s, ∀ y ∈ Submodule.span (𝓞 E) (s : Set (Fin r → E)),
      IsIntegral ℤ ((y0 : E) * herm G a y) := by
    intro a ha y hy'
    induction hy' using Submodule.span_induction with
    | mem b hb => exact hgen a ha b hb
    | zero => simpa [herm, cc] using isIntegral_zero
    | add u v _ _ hu hv => rw [herm_add_right, mul_add]; exact hu.add hv
    | smul c u _ hu => rw [herm_smul_right, mul_left_comm]; exact (isIntegral_cc c.2).mul hu
  have hall : ∀ x ∈ Submodule.span (𝓞 E) (s : Set (Fin r → E)), ∀ y ∈ Submodule.span (𝓞 E) (s : Set (Fin r → E)),
      IsIntegral ℤ ((y0 : E) * herm G x y) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem a ha => exact hright a ha
    | zero => intro y _; simpa [herm] using isIntegral_zero
    | add u v _ _ hu hv => intro y hy'; rw [herm_add_left, mul_add]; exact (hu y hy').add (hv y hy')
    | smul c u _ hu => intro y hy'; rw [herm_smul_left, mul_left_comm]; exact c.2.mul (hu y hy')
  refine ⟨y0.natAbs, Int.natAbs_pos.2 hy0, fun x hx y hy' => ?_⟩
  have key := hall x hx y hy'
  rcases Int.natAbs_eq y0 with h | h
  · have e : ((y0.natAbs : ℕ) : E) = (y0 : E) := by
      have h' := congrArg (fun z : ℤ => (z : E)) h
      simp only [Int.cast_natCast] at h'
      exact h'.symm
    rw [e]; exact key
  · have e : ((y0.natAbs : ℕ) : E) = -(y0 : E) := by
      have h' := congrArg (fun z : ℤ => (z : E)) h
      simp only [Int.cast_neg, Int.cast_natCast] at h'
      rw [h', neg_neg]
    rw [e, neg_mul]; exact key.neg

theorem exists_nat_int (k : E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : E) * k) := by
  have halg : IsAlgebraic ℤ k := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨y, hy, hyi⟩ := halg.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hyi
  rcases Int.natAbs_eq y with h | h
  · have e : ((y.natAbs : ℕ) : E) = (y : E) := by
      have h' := congrArg (fun z : ℤ => (z : E)) h
      simp only [Int.cast_natCast] at h'
      exact h'.symm
    rw [e]; exact hyi
  · have e : ((y.natAbs : ℕ) : E) = -(y : E) := by
      have h' := congrArg (fun z : ℤ => (z : E)) h
      simp only [Int.cast_neg, Int.cast_natCast] at h'
      rw [h', neg_neg]
    rw [e, neg_mul]; exact hyi.neg

theorem exists_princ_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (M : ℕ) (X0 : Data E r) (Λ : Submodule (𝓞 E) (Fin r → E)), 3 ≤ M → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ X : Data E r, X.Gm = X0.Gm ∧ X.Ψ = X0.Ψ ∧ X.p0 = X0.p0 ∧ X.Λ = Λ ∧ ∀ γ, γ ∈ X.Γ ↔ IsUStab X0.Gm Λ γ ∧ ∀ x ∈ Λ, ∃ y ∈ Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = M • y := by
  intro E _ _ _ r M X0 Λ hM hfg hsp
  obtain ⟨n, hn, hnint⟩ := exists_nat_herm_int X0.Gm Λ hfg
  obtain ⟨k, hk, hkint⟩ := exists_nat_int X0.κ0
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ,
      IsIntegral ℤ (((M * n * k : ℕ) : E) / (M : E) * X0.κ0 * herm X0.Gm x y) := by
    intro x hx y hy
    have e : ((M * n * k : ℕ) : E) / (M : E) * X0.κ0 * herm X0.Gm x y =
        ((k : E) * X0.κ0) * ((n : E) * herm X0.Gm x y) := by
      push_cast
      field_simp
    rw [e]
    exact hkint.mul (hnint x hx y hy)
  obtain ⟨X, hΨ, hG, hp, hΛ, -, -, -, hΓ, -⟩ := GlobalTheory.FlagData.exists_data GlobalTheory.latMinkowski E r X0.p0 M (M * n * k)
    X0.Ψ X0.Gm Λ X0.ξ0 X0.κ0 X0.cmType X0.Gm_herm X0.Gm_det X0.p0_le
    (fun τ hτ => X0.signature ⟨τ, hτ⟩) hfg hsp hM X0.ξ0_im X0.ξ0_ne X0.κ0_xi
    (fun τ hτ => X0.κ0_sign ⟨τ, hτ⟩) (by positivity) hint
  refine ⟨X, hG, hΨ, hp, hΛ, fun γ => ?_⟩
  rw [hΓ γ]
  refine and_congr Iff.rfl (forall₂_congr fun x _ => exists_congr fun y => and_congr Iff.rfl ?_)
  exact sub_eq_iff_eq_add'.symm

end GlobalTheory.PrincData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockMapOfCanonicalCommutationRelations
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.CCRFock
open MvPolynomial

theorem polEval_X {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (m : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V) (i : ι) (p : MvPolynomial ι ℂ) :
    polEval m hm f₀ (X i * p) = m i (polEval m hm f₀ p) := by
  simp [polEval, Module.End.mul_apply]

theorem polEval_one {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (m : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V) : polEval m hm f₀ 1 = f₀ := by
  simp [polEval]

theorem atPl_linear {W Λ : Type} [Fintype W] [DecidableEq W] (w : W) :
    ∃ L : Module.End ℂ (MvPolynomial Λ ℂ) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] _ : W, MvPolynomial Λ ℂ),
      ∀ A, L A = GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w A := ⟨(PiTensorProduct.mapMultilinear ℂ (fun _ : W => MvPolynomial Λ ℂ) (fun _ : W => MvPolynomial Λ ℂ)).toLinearMap
      (fun _ => LinearMap.id) w, fun A => by
    simp [GlobalTheory.RealLift.atPl]⟩

theorem fock_map_of_ccr : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ f₀ : V, f₀ ≠ 0 →
    (∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0) →
    ∃ Φ : (⨂[ℂ] _ : W, Pol P Q R S) →ₗ[ℂ] V, Function.Injective Φ ∧
      ∀ c T, Φ (sumPl (fun w => heisOp (c w)) T) = H c (Φ T) := by
  intro V _ _ W _ _ P Q R S H hadd hsmul hccr f₀ hf₀ hvac

  have hm : ∀ i j, fockM H i * fockM H j = fockM H j * fockM H i := _root_.GlobalTheory.CCRFock.fockM_comm H hadd hsmul hccr
  have hcr := _root_.GlobalTheory.CCRFock.CommDM.fockD_fockM_comm H hadd hsmul hccr

  have hd0 : ∀ j, fockD H j f₀ = 0 := by
    rintro ⟨w, a, b⟩
    have h := hvac w a b
    simp only [fockD, unitAt, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.add_apply]
    rw [h, smul_zero, neg_zero]
  have hpd := _root_.GlobalTheory.CCRFock.polEval_pderiv (fockM H) (fockD H) hm f₀ hcr hd0
  have hinj0 : Function.Injective (polEval (fockM H) hm f₀) :=
    GlobalTheory.T.injective_of_map_pderiv_eq_and_map_one_ne_zero _ (fockD H) hpd (by rw [polEval_one]; exact hf₀)
  refine ⟨polEval (fockM H) hm f₀ ∘ₗ polMap W (Ix P Q × Ix R S), hinj0.comp (_root_.GlobalTheory.CCRFock.polMap_injective W _), ?_⟩

  have hX : ∀ (w : W) (l : Ix P Q × Ix R S) T, polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S)
      (GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
        (LinearMap.mulLeft ℂ (MvPolynomial.X l)) T)) =
      fockM H (w, l) (polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S) T)) := by
    intro w l T
    have h := LinearMap.congr_fun (GlobalTheory.T.tensorPolynomialsToProductVariables_comp_mulLeft_X W (Ix P Q × Ix R S) w l) T
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at h
    rw [h, polEval_X]
  have hD : ∀ (w : W) (l : Ix P Q × Ix R S) T, polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S)
      (GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
        (MvPolynomial.pderiv l).toLinearMap T)) =
      fockD H (w, l) (polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S) T)) := by
    intro w l T
    have h := LinearMap.congr_fun (GlobalTheory.T.tensorPolynomialsToProductVariables_comp_pderiv W (Ix P Q × Ix R S) w l) T
    simp only [LinearMap.comp_apply, Derivation.coeFn_coe] at h
    rw [h, hpd]

  choose L hL using fun w : W => atPl_linear (Λ := Ix P Q × Ix R S) w
  intro c T
  have hsum : ∀ w, GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w (heisOp (c w)) =
      ∑ l : Ix P Q × Ix R S, ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * coefM (c w l.1 l.2) (lineSign l.1 l.2)) •
          GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
            (LinearMap.mulLeft ℂ (MvPolynomial.X l)) +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * coefD (c w l.1 l.2) (lineSign l.1 l.2)) •
          GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
            (MvPolynomial.pderiv l).toLinearMap) := by
    intro w
    clear hX hD hpd hinj0 hcr hm hd0 hvac hccr hsmul hadd hf₀
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hL w (heisOp (c w)), _root_.GlobalTheory.CCRFock.heisOp_eq_sum_mul_pderiv (c w), map_sum]
    simp only [map_add (f := _), map_smul]
    simp only [hL]
  rw [_root_.GlobalTheory.CCRFock.heis_expand H hadd hsmul c]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.RealLift.sumPl, hsum, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.add_apply, LinearMap.smul_apply, map_sum, map_add, map_smul, hX, hD]
  conv_rhs => rw [Fintype.sum_prod_type]

end GlobalTheory.CCRFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarishChandraReproducingFunctionGLinfinity
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic

namespace GlobalTheory.HCAlphaGLC

section

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

def topE : glG E a ≃ₜ* GL (Fin a) (Cinf E) where
  toMulEquiv := Subgroup.topEquiv
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

theorem exists_alpha : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))] (μ : Measure (GL (Fin a) (Cinf E))), μ.IsHaarMeasure → ∃ α : GL (Fin a) (Cinf E) → ℂ, Continuous α ∧ HasCompactSupport α ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ g, ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g := by
  intro E _ _ _ a L _ W hW X hX N _ _ μ hμ
  obtain ⟨p, hp0, hp⟩ := GlobalTheory.T.exists_laplacianPolynomial_kills_harishChandraFinite E a L W hW X hX N
  obtain ⟨d, b, P, hPm, -, hP⟩ := GlobalTheory.T.laplacianPolynomialKernel_of_polynomial_laplacian E a p hp0
  let e := topE E a
  letI : MeasurableSpace (glG E a) := borel _
  haveI : BorelSpace (glG E a) := ⟨rfl⟩
  let μ' : Measure (glG E a) := μ.map e.symm
  have hH : μ'.IsHaarMeasure := e.symm.isHaarMeasure_map μ
  obtain ⟨α', -, hc, hs, hα⟩ := @GlobalTheory.T.exists_smooth_convolution_eq_derivative (Matrix (Fin a) (Fin a) (Cinf E)) _ _ _ _ (glG E a) (glL E a) (glH E a) d b P hPm _ (by exact ⟨rfl⟩) μ' (by exact hH) []
  refine ⟨α' ∘ e.symm, ?_, ?_, fun φ hφ g => ?_⟩
  · exact hc.comp e.symm.continuous
  · exact hs.comp_homeomorph e.symm.toHomeomorph
  obtain ⟨hf, h0⟩ := (mem_solG _ _).1 (hP φ (hp φ hφ) g)
  have h1 := hα ⟨_, hf⟩ h0 1
  have hm : μ' = μ.map e.symm.toHomeomorph.toMeasurableEquiv := rfl
  rw [hm, integral_map_equiv] at h1
  simp only [one_mul, List.foldr_nil] at h1
  exact h1.trans (by simp [glRes])

end

end GlobalTheory.HCAlphaGLC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowerSectionNonzeroAtOriginStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundlePower_section_nonzero_at_origin : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ k : ℕ, 4 ≤ k → ∃ (t : SecA A F k) (c : F), c ≠ 0 ∧ ∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J).val := by
  first | exact @GlobalTheory.Poinc.Origin.exists_sec_value_ne_zero | exact GlobalTheory.Poinc.Origin.exists_sec_value_ne_zero | (intros; apply GlobalTheory.Poinc.Origin.exists_sec_value_ne_zero <;> assumption)
end

