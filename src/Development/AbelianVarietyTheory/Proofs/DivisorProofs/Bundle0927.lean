module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0889
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixInductionTransvectionDiagonal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.FormsLocus

theorem ΓSpecIso_inv_comp_specMap_appTop {W : Scheme.{0}} {A B : CommRingCat.{0}} (g : W ⟶ Spec B)
    (f : A ⟶ B) :
    (Scheme.ΓSpecIso A).inv ≫ (g ≫ Spec.map f).appTop =
      f ≫ (Scheme.ΓSpecIso B).inv ≫ g.appTop := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]

theorem factors_quot_iff (Rg : Type) [CommRing Rg] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) Rg))
    (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) :
    (∃ w : T ⟶ Sp (MvPolynomial (Fin n) Rg ⧸ I),
      w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = g) ↔
      ∀ P ∈ I, GlobalTheory.FormsLocus.ringOf g P = 0 := by
  constructor
  · rintro ⟨w, rfl⟩ P hP
    have h := congrArg (fun k => k.hom P)
      (ΓSpecIso_inv_comp_specMap_appTop w (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    change ((w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv.hom P)) = 0
    rw [h, Ideal.Quotient.eq_zero_iff_mem.2 hP, map_zero, map_zero]
  · intro h
    let φ : CommRingCat.of (MvPolynomial (Fin n) Rg) ⟶ Γ(T, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv ≫ g.appTop
    refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I φ.hom h)), ?_⟩
    rw [Category.assoc, ← Spec.map_comp]
    change T.toSpecΓ ≫ Spec.map φ = g
    apply ext_of_isAffine
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv,
      ΓSpecIso_inv_comp_specMap_appTop, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

end GlobalTheory.FormsLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPowOfPsiAtTrivial
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.GaussModulus

namespace GlobalTheory.GaussModulus

theorem mem_pow_of_psiAt_trivial {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (c : Eˣ)
    (hc : w.valuation E (c : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ))) (δ : 𝓞 E)
    (hδ : ∀ r : 𝓞 E, psiAt w (algebraMap E (w.adicCompletion E) ((δ : E) * r / c)) = 1) : δ ∈ w.asIdeal ^ a := by
  set t : w.adicCompletion E := algebraMap E (w.adicCompletion E) ((δ : E) / c) with ht
  have hc0 : w.valuation E (c : E) ≠ 0 := by rw [hc]; exact WithZero.exp_ne_zero
  have hδ1 : w.valuation E (δ : E) ≤ 1 := w.valuation_le_one δ
  have hvt : Valued.v t ≤ WithZero.exp (((a + diffExp w : ℕ) : ℤ)) := by
    rw [ht, valued_algebraMap, map_div₀, hc, div_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), ← WithZero.exp_add]
    simpa using hδ1
  have key : ∀ s ∈ w.adicCompletionIntegers E, psiAt w (t * s) = 1 := by
    intro s hs
    have hs1 : Valued.v s ≤ 1 := hs
    obtain ⟨r, hr⟩ := exists_int_approx w hs1 (a + diffExp w)
    have e : t * s = algebraMap E (w.adicCompletion E) ((δ : E) * r / c) +
        t * (s - algebraMap E (w.adicCompletion E) (r : E)) := by
      have ha : algebraMap E (w.adicCompletion E) ((δ : E) * r / c) =
          algebraMap E (w.adicCompletion E) ((δ : E) / c) * algebraMap E (w.adicCompletion E) (r : E) := by
        rw [← (algebraMap E (w.adicCompletion E)).map_mul]; congr 1; ring
      rw [ha, ht]
      ring
    rw [e, psiAt_add, hδ r, one_mul]
    refine psiAt_eq_one ?_
    rw [map_mul]
    calc Valued.v t * Valued.v (s - algebraMap E (w.adicCompletion E) (r : E))
        ≤ WithZero.exp (((a + diffExp w : ℕ) : ℤ)) * WithZero.exp (-((a + diffExp w : ℕ) : ℤ)) :=
          mul_le_mul' hvt hr
      _ = 1 := by rw [← WithZero.exp_add]; simp
      _ ≤ WithZero.exp (diffExp w : ℤ) := by
          rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have hvt' := (psiAt_conductor w t).1 key
  rw [ht, valued_algebraMap, map_div₀, hc, div_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), ← WithZero.exp_add] at hvt'
  have h2 : w.valuation E (δ : E) ≤ WithZero.exp (-(a : ℤ)) := by
    refine hvt'.trans (le_of_eq ?_)
    congr 1
    push_cast
    ring
  rw [w.valuation_of_algebraMap] at h2
  exact (w.intValuation_le_pow_iff_mem δ a).1 (by simpa using h2)

end GlobalTheory.GaussModulus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolySeparableOfNoSqZeroPolynomialImage
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.LKCx

theorem minpoly_separable_of_sq_zero_free
    (F C : Type) [Field F] [Ring C] [IsSimpleRing C] [Algebra F C] [FiniteDimensional F C]
    (n : ℕ) (σ : F →+* ℂ) (ψ : C →+* Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    (hψ : ∀ x : F, ψ (algebraMap F C x) = Matrix.scalar (Fin n) (σ x)) (c : C)
    (hc : ∀ P : Polynomial ℂ, Polynomial.aeval (ψ c) P * Polynomial.aeval (ψ c) P = 0 →
      Polynomial.aeval (ψ c) P = 0) :
    (minpoly F c).Separable := by
  haveI : CharZero F := (RingHom.charZero_iff σ.injective).2 inferInstance
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hinj : Function.Injective ψ := ψ.injective
  have hcomp : ψ.comp (algebraMap F C) = (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)).comp σ := by
    ext x
    simp only [RingHom.comp_apply, hψ, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
    rfl
  have hev : ∀ Q : Polynomial F, ψ (Polynomial.aeval c Q) = Polynomial.aeval (ψ c) (Q.map σ) := by
    intro Q
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp, Polynomial.aeval_def,
      Polynomial.eval₂_map]
  have hint : IsIntegral F c := IsIntegral.of_finite F c
  have hm0 : minpoly F c ≠ 0 := minpoly.ne_zero hint
  rw [PerfectField.separable_iff_squarefree]
  intro g hg
  obtain ⟨h, hh⟩ := hg
  have hQ : Polynomial.aeval c (g * h) = 0 := by
    apply hinj
    rw [map_zero, hev]
    apply hc
    rw [← hev, ← map_mul, ← map_mul]
    have : g * h * (g * h) = minpoly F c * h := by rw [hh]; ring
    rw [this, map_mul, minpoly.aeval, zero_mul, map_zero]
  have hdvd : minpoly F c ∣ g * h := minpoly.dvd F c hQ
  have hgh0 : g * h ≠ 0 := by
    intro h0
    apply hm0
    rw [hh, mul_assoc, h0, mul_zero]
  rw [hh, mul_assoc] at hdvd
  have : g * (g * h) ∣ 1 * (g * h) := by rwa [one_mul]
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hgh0).1 this)

end GlobalTheory.LKCx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicCellFiniteUnionLocalDoubleCosets
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JSW.MirPatch.Decomp

open GlobalTheory.JSW GlobalTheory.SmGL Topology

theorem exists_distinct {ι X : Type} [Finite ι] (C : ι → Set X)
    (hC : ∀ i j x, x ∈ C i → x ∈ C j → C i = C j) :
    ∃ (N : ℕ) (f : Fin N → ι), (∀ i j x, x ∈ C (f i) → x ∈ C (f j) → i = j) ∧
      ∀ x, (∃ i, x ∈ C i) ↔ ∃ j, x ∈ C (f j) := by
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (Set.range C)
  have hf : ∀ j, C (e.symm j).2.choose = (e.symm j).1 := fun j => (e.symm j).2.choose_spec
  refine ⟨N, fun j => (e.symm j).2.choose, fun i j x hi hj => ?_, fun x => ⟨fun ⟨i, hi⟩ => ?_, fun ⟨j, hj⟩ => ⟨_, hj⟩⟩⟩
  · have h := hC _ _ x hi hj
    rw [hf, hf] at h
    exact e.symm.injective (Subtype.ext h)
  · refine ⟨e ⟨C i, i, rfl⟩, ?_⟩
    simp only
    rw [hf, Equiv.symm_apply_apply]
    exact hi

theorem exists_finite_reps {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K A : Set G} (hK : IsCompact K) (hA : A ⊆ K) (V : Subgroup G) (hV : IsOpen (V : Set G)) :
    ∃ (ι : Type) (_ : Finite ι) (k : ι → G), (∀ i, k i ∈ A) ∧ ∀ a ∈ A, ∃ i, (k i)⁻¹ * a ∈ V := by
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hK (V := (V : Set G))
    (by rw [hV.interior_eq]; exact ⟨1, V.one_mem⟩)
  let ι := {g : G // g ∈ t ∧ ∃ a ∈ A, g * a ∈ V}
  haveI : Finite ι := Finite.of_injective (fun x : ι => (⟨x.1, x.2.1⟩ : t))
    (fun x y h => Subtype.ext (congrArg (fun z : t => (z : G)) h))
  refine ⟨ι, inferInstance, fun x => x.2.2.choose, fun x => x.2.2.choose_spec.1, fun a ha => ?_⟩
  obtain ⟨g, hg, hga⟩ := Set.mem_iUnion₂.1 (ht (hA ha))
  have hga' : g * a ∈ V := hga
  refine ⟨⟨g, hg, a, ha, hga'⟩, ?_⟩
  have hb := (⟨g, hg, a, ha, hga'⟩ : ι).2.2.choose_spec.2
  have e : ((⟨g, hg, a, ha, hga'⟩ : ι).2.2.choose)⁻¹ * a =
      (g * (⟨g, hg, a, ha, hga'⟩ : ι).2.2.choose)⁻¹ * (g * a) := by group
  rw [e]
  exact mul_mem (inv_mem hb) hga'

theorem cell_eq_of_mem {F : Type} [NormedField F] {n : ℕ} {z g : GL (Fin n) F} {U : Subgroup (GL (Fin n) F)}
    (h : g ∈ Cut.cell z (U : Set (GL (Fin n) F))) :
    Cut.cell z (U : Set (GL (Fin n) F)) = Cut.cell g (U : Set (GL (Fin n) F)) := by
  obtain ⟨u, hu, k, hk, rfl⟩ := h
  ext x
  constructor
  · rintro ⟨u', hu', k', hk', rfl⟩
    exact ⟨u' * u⁻¹, mul_mem hu' (inv_mem hu), k⁻¹ * k', mul_mem (inv_mem hk) hk', by group⟩
  · rintro ⟨u', hu', k', hk', rfl⟩
    exact ⟨u' * u, mul_mem hu' hu, k * k', mul_mem hk hk', by group⟩

variable {E : Type} [Field E] [NumberField E]

theorem map_comp_eq {a : ℕ} (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := rfl

theorem af_eq {x y : Af E} (h : ∀ w, pLoc E w x = pLoc E w y) : x = y := FiniteAdeleRing.ext _ h


open Classical in
theorem pLoc_list_prod {n : ℕ} (u : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin n) (w.adicCompletion E))
    (l : List (HeightOneSpectrum (𝓞 E))) (hl : l.Nodup) (v : HeightOneSpectrum (𝓞 E)) :
    GeneralLinearGroup.map (pLoc E v) (l.map fun w => locGL E n w (u w)).prod = if v ∈ l then u v else 1 := by
  classical
  induction l with
  | nil => simp
  | cons w l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih (List.nodup_cons.1 hl).2]
    by_cases h : v = w
    · subst h
      rw [pLoc_locGL, if_neg (List.nodup_cons.1 hl).1, if_pos (by simp), mul_one]
    · rw [pLoc_locGL_of_ne h, one_mul]
      simp only [List.mem_cons, h, false_or]

theorem loc_mem_unipB {a : ℕ} {u : GA E a} (hu : u ∈ NA (E := E) (a := a)) (w : HeightOneSpectrum (𝓞 E)) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) u ∈ unipB (w.adicCompletion E) (Fin a) :=
  (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j h => by
    show pLoc E w (pFin E _) = 0
    rw [hu.1 i j h, map_zero, map_zero], fun i => by
    show pLoc E w (pFin E _) = 1
    rw [hu.2 i, map_one, map_one]⟩

variable [_root_.NumberField.IsTotallyComplex E]

theorem finGL_mem_NA {a : ℕ} {v : GL (Fin a) (Af E)}
    (hv : ∀ w, GeneralLinearGroup.map (pLoc E w) v ∈ unipB (w.adicCompletion E) (Fin a)) : finGL E a v ∈ NA (E := E) (a := a) := by
  have e1 : ∀ i j, pInf E ((finGL E a v : Matrix (Fin a) (Fin a) (Ad E)) i j) =
      ((1 : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j := fun i j =>
    congrArg (fun g : GL (Fin a) (Cinf E) => (g : Matrix (Fin a) (Fin a) (Cinf E)) i j) (pInf_finGL (E := E) v)
  have e2 : ∀ i j, pFin E ((finGL E a v : Matrix (Fin a) (Fin a) (Ad E)) i j) = (v : Matrix (Fin a) (Fin a) (Af E)) i j :=
    fun i j => congrArg (fun g : GL (Fin a) (Af E) => (g : Matrix (Fin a) (Fin a) (Af E)) i j) (pFin_finGL (E := E) v)
  refine ⟨fun i j h => ad_ext ?_ ?_, fun i => ad_ext ?_ ?_⟩
  · rw [e1, Units.val_one, Matrix.one_apply_ne (ne_of_gt h), map_zero]
  · rw [e2, map_zero]
    exact af_eq fun w => by rw [map_zero]; exact ((GlobalTheory.SmGL.mem_unipB _).1 (hv w)).1 i j h
  · rw [e1, Units.val_one, Matrix.one_apply_eq, map_one]
  · rw [e2, map_one]
    exact af_eq fun w => by rw [map_one]; exact ((GlobalTheory.SmGL.mem_unipB _).1 (hv w)).2 i

theorem mem_cell_iff {a : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin a) (Af E))) (q : GA E a)
    {p : GA E a} (hp : p ∈ supS (E := E) (a := a) S) :
    p ∈ cell K q ↔ ∃ k ∈ K,
      (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) q * k) ∈
        unipB (w.adicCompletion E) (Fin a)) ∧
      ∀ w ∈ S, ∃ u ∈ unipB (w.adicCompletion E) (Fin a), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p =
        u * GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) q * k) := by
  constructor
  · rintro ⟨u, hu, k, hk, y, rfl⟩
    have hf : GeneralLinearGroup.map (pFin E) (u * q * finGL E a k * infGL E a y) =
        GeneralLinearGroup.map (pFin E) u * (GeneralLinearGroup.map (pFin E) q * k) := by
      rw [map_mul, map_mul, map_mul, pFin_finGL, pFin_infGL, mul_one, mul_assoc]
    refine ⟨k, hk, fun w hw => ?_, fun w _ => ⟨_, loc_mem_unipB hu w, ?_⟩⟩
    · have h1 := hp w hw
      rw [map_comp_eq, hf, map_mul] at h1
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_mem (loc_mem_unipB hu w)
    · rw [map_comp_eq, hf, map_mul, map_comp_eq]
  · rintro ⟨k, hk, hout, hin⟩
    set v := GeneralLinearGroup.map (pFin E) p * (GeneralLinearGroup.map (pFin E) q * k)⁻¹ with hv
    have hvN : ∀ w, GeneralLinearGroup.map (pLoc E w) v ∈ unipB (w.adicCompletion E) (Fin a) := by
      intro w
      rw [hv, map_mul, map_inv]
      by_cases hw : w ∈ S
      · obtain ⟨u, hu, he⟩ := hin w hw
        rw [← map_comp_eq, he, mul_inv_cancel_right]
        exact hu
      · rw [← map_comp_eq, hp w hw, one_mul]
        exact inv_mem (hout w hw)
    refine ⟨finGL E a v, finGL_mem_NA hvN, k, hk,
      (GeneralLinearGroup.map (pInf E) q)⁻¹ * GeneralLinearGroup.map (pInf E) p, ga_ext ?_ ?_⟩
    · simp only [map_mul, pInf_finGL, pInf_infGL, one_mul, mul_one, mul_inv_cancel_left]
    · simp only [map_mul, pFin_finGL, pFin_infGL, mul_one, hv]
      group

end GlobalTheory.JSW.MirPatch.Decomp

namespace GlobalTheory.JSW.MirPatch

open GlobalTheory.JSW GlobalTheory.SmGL Decomp

theorem cell_decomp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (N : ℕ) (z : Fin N → ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, IsCompact (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ IsOpen (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) ∧ (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ i j : Fin N, (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z j w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → i = j) ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), (p ∈ GlobalTheory.JSW.MirPatch.cell K q ↔ ∃ i : Fin N, ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) := by
  intro E _ _ _ m S K hKo hKc q
  classical
  choose U hUo hUc hUK using fun w => LocEx.exists_compact_open (a := m + 1) w K hKo
  set qf := GeneralLinearGroup.map (pFin E) q with hqf
  let A : Set (GL (Fin (m + 1)) (Af E)) := {k | k ∈ K ∧ ∀ w ∉ S,
    GeneralLinearGroup.map (pLoc E w) (qf * k) ∈ unipB (w.adicCompletion E) (Fin (m + 1))}
  let V : Subgroup (GL (Fin (m + 1)) (Af E)) :=
    { carrier := {v | ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) v ∈ U w}
      mul_mem' := fun ha hb w hw => by rw [map_mul]; exact mul_mem (ha w hw) (hb w hw)
      one_mem' := fun w _ => by rw [map_one]; exact one_mem _
      inv_mem' := fun ha w hw => by rw [map_inv]; exact inv_mem (ha w hw) }
  have hVo : IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) := by
    have e : (V : Set (GL (Fin (m + 1)) (Af E))) =
        ⋂ w ∈ S, GeneralLinearGroup.map (pLoc E w) ⁻¹' (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) := by
      ext v; simp [V]
    rw [e]
    exact isOpen_biInter_finset fun w _ => (hUo w).preimage (LocEx.continuous_map_pLoc w)
  obtain ⟨ι, _, k, hkA, hcov⟩ := exists_finite_reps (A := A) hKc (fun x hx => hx.1) V hVo
  let C : ι → Set (∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)) := fun i =>
    {x | ∀ w ∈ S, x w ∈ Cut.cell (GeneralLinearGroup.map (pLoc E w) (qf * k i))
      (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}
  have hC : ∀ i j x, x ∈ C i → x ∈ C j → C i = C j := by
    intro i j x hi hj
    ext y
    exact forall₂_congr fun w hw => by rw [cell_eq_of_mem (hi w hw), cell_eq_of_mem (hj w hw)]
  obtain ⟨N, f, huniq, hiff⟩ := exists_distinct C hC
  refine ⟨U, N, fun j w => GeneralLinearGroup.map (pLoc E w) (qf * k (f j)), fun w _ => ⟨hUc w, hUo w, hUK w⟩,
    fun p _ i j hi hj => huniq i j (fun w => GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p) hi hj,
    fun p hp => ?_⟩
  rw [mem_cell_iff S K q hp.1]
  refine Iff.trans ?_ (hiff (fun w => GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p))
  constructor
  · rintro ⟨k', hk', hout, hin⟩
    obtain ⟨i, hi⟩ := hcov k' ⟨hk', hout⟩
    refine ⟨i, fun w hw => ?_⟩
    obtain ⟨u, hu, he⟩ := hin w hw
    refine ⟨u, hu, GeneralLinearGroup.map (pLoc E w) ((k i)⁻¹ * k'), hi w hw, ?_⟩
    show GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = _
    rw [he, mul_assoc u, ← map_mul, mul_assoc, mul_inv_cancel_left]
  · rintro ⟨i, hi⟩
    choose! uu huu cc hcc heq using hi
    let g : GL (Fin (m + 1)) (Af E) := (S.toList.map fun w => locGL E (m + 1) w (cc w)).prod
    have hgK : g ∈ K := by
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      exact hUK w _ (hcc w (Finset.mem_toList.1 hw))
    have hg : ∀ v, GeneralLinearGroup.map (pLoc E v) g = if v ∈ S then cc v else 1 := fun v => by
      rw [pLoc_list_prod cc _ S.nodup_toList v]
      simp only [Finset.mem_toList]
    refine ⟨k i * g, mul_mem (hkA i).1 hgK, fun w hw => ?_, fun w hw => ⟨uu w, huu w hw, ?_⟩⟩
    · rw [← mul_assoc, map_mul, hg w, if_neg hw, mul_one]
      exact (hkA i).2 w hw
    · refine (heq w hw).trans ?_
      rw [← mul_assoc qf, map_mul (GeneralLinearGroup.map (pLoc E w)) (qf * k i) g, hg w, if_pos hw, mul_assoc]

end GlobalTheory.JSW.MirPatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulEqOfOrth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open GlobalTheory.Ker GlobalTheory.IndefiniteRowSideFullHecke Filter Topology
open scoped TensorProduct ComplexConjugate ComplexOrder Classical ENNReal

namespace GlobalTheory.VacuumFrameCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem af_ext {α β : Af D.host.F} (h : ∀ w, evalV D.host.F w α = evalV D.host.F w β) : α = β :=
  FiniteAdeleRing.ext _ h

theorem place_orth {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hv : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := h
  obtain ⟨β, rfl, -, k0⟩ := h'
  refine Prod.ext (mul_zero (0 : Ainf D.host.F)) (show α * β = 0 from af_ext fun w => ?_)
  rw [map_mul, map_zero]
  by_cases hw : w = v
  · rw [k0 w (hw ▸ hv), mul_zero]
  · rw [h0 w hw, zero_mul]

end GlobalTheory.VacuumFrameCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultRealElt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealEquiv

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : Datum.InfFam D} {M : DSModel V S}
  {J : Set (GA D V)} {χ : GA D V → ℂ}


open Classical in
theorem list_equiv {U : MMap M} (hU : IsMultMap θ M J χ U)
    (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : ∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ))
    (v w : M.Vec) (h : ∀ ρ, (w ρ : M.H ρ) = M.rep ρ (g ρ) (v ρ : M.H ρ)) (l : List D.what₂.Tau) (hl : l.Nodup) :
    U (fun ρ => if ρ ∈ l then w ρ else v ρ) = rTr V (l.map fun ρ => atTau θ V ρ (g ρ)).prod (U v) := by
  induction l with
  | nil =>
    funext x
    simp [rTr]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have e := hU.equiv a (g a) (hg a) (fun ρ => if ρ ∈ l then w ρ else v ρ) (w a) (by
      simp only [if_neg hl.1]; exact h a)
    rw [ih hl.2] at e
    have e2 : rTr V ((a :: l).map fun ρ => atTau θ V ρ (g ρ)).prod (U v) =
        rTr V (atTau θ V a (g a)) (rTr V (l.map fun ρ => atTau θ V ρ (g ρ)).prod (U v)) := by
      funext x
      simp only [rTr, List.map_cons, List.prod_cons, mul_assoc]
    rw [e2, ← e]
    congr 1
    funext ρ
    by_cases hρ : ρ = a
    · subst hρ
      simp
    · rw [Function.update_of_ne hρ]
      simp [hρ]

theorem mult_realElt : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : Datum.InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ U ∈ Mult θ M J χ, ∀ g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ)) → ∀ v w : M.Vec, (∀ ρ, (w ρ : M.H ρ) = M.rep ρ (g ρ) (v ρ : M.H ρ)) → U w = rTr V (realElt θ V g) (U v) := by
  intro D V S θ M J χ U hU g hg v w h
  classical
  induction hU using Submodule.span_induction with
  | mem U hU =>
    have e := list_equiv hU g hg v w h (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _)
    rw [realElt, ← e]
    congr 1
    funext ρ
    simp
  | zero => funext x; simp [rTr]
  | add U U' _ _ h1 h2 =>
    funext x
    have a := congrFun h1 x
    have b := congrFun h2 x
    simp only [rTr, MultilinearMap.add_apply, Pi.add_apply] at a b ⊢
    rw [a, b]
  | smul c U _ h1 =>
    funext x
    have a := congrFun h1 x
    simp only [rTr, MultilinearMap.smul_apply, Pi.smul_apply] at a ⊢
    rw [a]

end GlobalTheory.RealEquiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicCoeffDenominatorBoundOfBoundedRootsStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_coeff_denominator_bound_of_bounded_roots : ∀ (p : ℕ) [Fact p.Prime] (q : Polynomial ℚ), q.Monic → ∀ k : ℕ, (∀ μ : PadicAlgCl p, (q.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ (p : ℝ) ^ k) → ∀ i, ∃ m : ℕ, m.Coprime p ∧ ∃ a : ℤ, ((p ^ (k * q.natDegree) * m : ℕ) : ℚ) * q.coeff i = a := by
  first | (exact @GlobalTheory.padic_denom_coeff_of_roots_bounded) | (exact GlobalTheory.padic_denom_coeff_of_roots_bounded) | (intros; apply GlobalTheory.padic_denom_coeff_of_roots_bounded  <;> assumption)
end

