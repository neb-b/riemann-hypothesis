module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import GroundTheory.GlobalFields.SemilocalAlgebras.Finite
public import GroundTheory.GlobalFields.TateThesis.ChebotarevAbelian
public import GroundTheory.GlobalFields.TateThesis.Bundle0002
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.EtaQuad
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

namespace UpperTheory.ConvolutionTheory.R2.C.QuadraticHeckeCharacter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem normV_abs {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    normV w = Ideal.absNorm w.asIdeal := by
  rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

private theorem normV_eq_pow (w : HeightOneSpectrum (𝓞 E)) :
    normV w = normV (w.under (𝓞 F)) ^ w.asIdeal.inertiaDeg (𝓞 F) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 F)).isMaximal
  rw [normV_abs, normV_abs, ← Ideal.absNorm_relNorm (𝓞 F) (𝓞 E) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 F)).asIdeal, map_pow]

private theorem one_lt_normV {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    1 < normV v := by
  rw [normV_abs]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

private theorem under_of_mem {v : HeightOneSpectrum (𝓞 F)} (u : SemiLocal.PlacesOver E v) : u.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext u.2.over.symm

private theorem inertiaDeg_pos (w : HeightOneSpectrum (𝓞 E)) : 0 < w.asIdeal.inertiaDeg (𝓞 F) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 F)).isMaximal
  rw [← Ideal.inertiaDeg'_eq_inertiaDeg (w.under (𝓞 F)).asIdeal w.asIdeal]
  exact Ideal.inertiaDeg'_pos _ _

private theorem finite_bad :
    {w : HeightOneSpectrum (𝓞 E) | ¬ Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 F))}.Finite := by
  refine (Set.Finite.preimage' (f := fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 F))
    (finite_setOf_exists_ramificationIdx_ne_one F E) fun v _ => ?_).subset fun w hw => ?_
  · exact (Set.finite_range fun u : SemiLocal.PlacesOver E v => u.1).subset fun w hw =>
      ⟨⟨w, ⟨by rw [← (Set.mem_singleton_iff.1 hw)]; rfl⟩⟩, rfl⟩
  · obtain ⟨u, hu, he⟩ : ∃ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = w.under (𝓞 F) ∧
        u.asIdeal.ramificationIdx (𝓞 F) ≠ 1 := by
      have hw' : ¬ Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 F)) := hw
      simpa only [GlobalTheory.LFun.isUnram_iff, not_forall, exists_prop, ne_eq] using hw'
    exact ⟨u, ⟨by change (w.under (𝓞 F)).asIdeal = _; rw [← hu]; rfl⟩, he⟩

private theorem isSplit_iff_normV (h2 : Module.finrank F E = 2) (w : HeightOneSpectrum (𝓞 E))
    (hu : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 F))) :
    Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 F)) ↔ normV w = normV (w.under (𝓞 F)) := by
  have hsum := SemiLocal.sum_ramificationIdx_mul_inertiaDeg E (w.under (𝓞 F))
  rw [h2] at hsum
  have hterm : ∀ u : SemiLocal.PlacesOver E (w.under (𝓞 F)),
      u.1.asIdeal.ramificationIdx (𝓞 F) * u.1.asIdeal.inertiaDeg (𝓞 F) = u.1.asIdeal.inertiaDeg (𝓞 F) :=
    fun u => by rw [GlobalTheory.LFun.isUnram_iff.1 hu u.1 (under_of_mem u), one_mul]
  simp only [hterm] at hsum
  let w₀ : SemiLocal.PlacesOver E (w.under (𝓞 F)) := ⟨w, ⟨rfl⟩⟩
  have h1 : 1 < normV (w.under (𝓞 F)) := one_lt_normV _
  constructor
  · intro hs
    obtain ⟨P, Q, hPQ, hP, hQ⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    obtain ⟨u, hu', hne⟩ : ∃ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = w.under (𝓞 F) ∧ u ≠ w := by
      by_cases h : P = w
      · exact ⟨Q, hQ, fun e => hPQ (h.trans e.symm)⟩
      · exact ⟨P, hP, h⟩
    let u₀ : SemiLocal.PlacesOver E (w.under (𝓞 F)) := ⟨u, ⟨by rw [← hu']; rfl⟩⟩
    have hne' : w₀ ≠ u₀ := fun e => hne (congrArg Subtype.val e).symm
    have hle := Finset.add_le_sum (f := fun u : SemiLocal.PlacesOver E (w.under (𝓞 F)) => u.1.asIdeal.inertiaDeg (𝓞 F))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ w₀) (Finset.mem_univ u₀) hne'
    rw [hsum] at hle
    have p1 : 0 < w.asIdeal.inertiaDeg (𝓞 F) := inertiaDeg_pos w
    have p2 : 0 < u.asIdeal.inertiaDeg (𝓞 F) := inertiaDeg_pos u
    have hf : w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
      change w.asIdeal.inertiaDeg (𝓞 F) + u.asIdeal.inertiaDeg (𝓞 F) ≤ 2 at hle
      omega
    rw [normV_eq_pow (F := F) w, hf, pow_one]
  · intro hn
    by_contra hs
    have hall : ∀ u : SemiLocal.PlacesOver E (w.under (𝓞 F)), u = w₀ := fun u =>
      Subtype.ext (GlobalTheory.LFun.eq_of_not_isSplit hs (under_of_mem u) rfl)
    rw [Finset.sum_eq_single w₀ (fun b _ hb => absurd (hall b) hb) (by simp)] at hsum
    change w.asIdeal.inertiaDeg (𝓞 F) = 2 at hsum
    rw [normV_eq_pow (F := F) w, hsum] at hn
    nlinarith

end UpperTheory.ConvolutionTheory.R2.C.QuadraticHeckeCharacter

theorem UpperTheory.ConvolutionTheory.R2.C.etaQuad :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E], ∃ η : HChar F, IsQuadCharOf E η ∧
    ∀ a, ((η.1 a : ℂˣ) : ℂ) = (((GlobalTheory.IdeleNormChar.normSign E a : ℤˣ) : ℤ) : ℂ) := by
  intro F E _ _ _ _ _ _
  have h2 : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  obtain ⟨η, hη, -⟩ := GlobalTheory.IdeleNormChar.globalNormIndexTwo F E h2
  have hη' : GlobalTheory.LFun.IsEta F E η := hη
  have he := hη'.eq_normSign
  refine ⟨GlobalTheory.LFun.toHChar η hη'.isHeckeF, ?_, fun a => ?_⟩
  · have hfin := QuadraticHeckeCharacter.finite_bad (F := F) (E := E)
    filter_upwards [hfin.compl_mem_cofinite] with w hw v hv
    have hw' : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 F)) := by simpa using hw
    obtain rfl : w.under (𝓞 F) = v := GlobalTheory.LFun.comap_eq_iff.1 hv.symm
    refine ⟨(hη'.unrAt_iff h2).2 hw', ?_⟩
    rw [hη'.val_eq h2 hw']
    unfold GlobalTheory.LFun.etaU
    have hi := QuadraticHeckeCharacter.isSplit_iff_normV h2 w hw'
    by_cases hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 F))
    · rw [if_pos hs, if_pos (hi.1 hs)]
    · rw [if_neg hs, if_neg (mt hi.2 hs)]
  · have h3 : ((GlobalTheory.LFun.toHChar η hη'.isHeckeF).1 a : ℂ) = ((η a : Circle) : ℂ) := rfl
    rw [h3, he, MonoidHom.comp_apply]
    rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with e | e <;>
      simp [e, GlobalTheory.IdeleNormChar.signToCircle]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.GaussS
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private noncomputable def gaussEquiv (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ι : Type) [Fintype ι] :
    (ι → NumberField.mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (ι × InfinitePlace F) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => WithLp.toLp 2 fun p => (x p.1).1 ⟨p.2, IsTotallyReal.isReal p.2⟩
      map_add' := fun x y => by ext p; simp
      map_smul' := fun c x => by ext p; simp
      invFun := fun y i => (fun w => y (i, w.1), fun _ => 0)
      left_inv := fun x => by
        funext i
        refine Prod.ext (funext fun w => rfl) (funext fun w => ?_)
        exact absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.2 w.2)
      right_inv := fun y => by ext p; rfl }

private theorem gaussEquiv_apply {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ι : Type} [Fintype ι]
    (v : ι → A F) (p : ι × InfinitePlace F) :
    gaussEquiv F ι (infPartPi v) p = TR.pInf F (v p.1) p.2 := by
  change (infPartPi v p.1).1 ⟨p.2, IsTotallyReal.isReal p.2⟩ = _
  simp only [infPartPi, homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  change _ = InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal p.2) ((v p.1).1 p.2)
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]

theorem UpperTheory.ConvolutionTheory.R2.C.gaussS :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ι : Type) [Fintype ι] (g : FiniteAdeleRing (𝓞 F) F → ℂ), g ∈ finiteSchwartzBruhat F → (fun v : ι → A F => ∏ i, g1 g (v i)) ∈ schwartzBruhatPi (K := F) (ι := ι) := by
  intro F _ _ _ ι _ g hg
  have h := schwartzBruhatTensorPi_mem
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (gaussEquiv F ι)
      (gaussianSchwartz (EuclideanSpace ℝ (ι × InfinitePlace F))))
    (finiteTensor_mem (ι := ι) fun _ => hg)
  convert h using 1
  funext v
  have hn : ‖gaussEquiv F ι (infPartPi v)‖ ^ 2 = ∑ i, ∑ w, TR.pInf F (v i) w ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w _ => by rw [gaussEquiv_apply]
  simp only [schwartzBruhatTensorPi, finiteTensor, g1, Finset.prod_mul_distrib,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, gaussianSchwartz_apply, hn]
  congr 1
  · push_cast
    rw [Finset.mul_sum, Complex.exp_sum]
    refine (Finset.prod_congr rfl fun i _ => ?_)
    rw [Finset.mul_sum, Complex.exp_sum]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.GenLoc
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.genLoc :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (s : Finset (R × R)), (∀ p ∈ s, IsUnit p.1 ∨ IsUnit p.2) →
    (s.card : ℕ∞) < ENat.card (IsLocalRing.ResidueField R) → ∃ t : R, ∀ p ∈ s, IsUnit (p.1 + p.2 * t) := by
  intro R _ _ s hs hcard
  let f : R × R → IsLocalRing.ResidueField R := fun p =>
    -(IsLocalRing.residue R p.1) / (IsLocalRing.residue R p.2)
  have hex : ∃ u : IsLocalRing.ResidueField R, u ∉ s.image f := by
    by_contra hall
    have hall' : ∀ u : IsLocalRing.ResidueField R, u ∈ s.image f := by
      intro u
      by_contra hu
      exact hall ⟨u, hu⟩
    have hsub : (Set.univ : Set (IsLocalRing.ResidueField R)) ⊆ ((s.image f : Finset _) : Set _) :=
      fun u _ => by simpa using hall' u
    have h1 : ENat.card (IsLocalRing.ResidueField R) ≤ ((s.image f).card : ℕ∞) := by
      have h2 := Set.encard_le_encard hsub
      rwa [Set.encard_univ, Set.encard_coe_eq_coe_finsetCard] at h2
    have h3 : ((s.image f).card : ℕ∞) ≤ (s.card : ℕ∞) := by
      exact_mod_cast Finset.card_image_le
    exact absurd (lt_of_le_of_lt (h1.trans h3) hcard) (lt_irrefl _)
  obtain ⟨u, hu⟩ := hex
  obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective u
  refine ⟨t, fun p hp => ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_add (f := _), map_mul]
  intro h0
  by_cases hb : IsLocalRing.residue R p.2 = 0
  · rw [hb, zero_mul, add_zero] at h0
    rcases hs p hp with h | h
    · exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 h h0
    · exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 h hb
  · apply hu
    refine Finset.mem_image.2 ⟨p, hp, ?_⟩
    show -(IsLocalRing.residue R p.1) / (IsLocalRing.residue R p.2) = _
    rw [div_eq_iff hb]
    linear_combination -h0
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.GrpRel
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

section
variable {F : Type} [Field F] [NumberField F]

private lemma nU_val (b : A F) : (nU b).1 = !![1, b; 0, 1] := rfl
private lemma mD_val (a : (A F)ˣ) : (mD a).1 = !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)] := rfl
private lemma wW_val : (wW F).1 = !![0, 1; -1, 0] := rfl

private lemma sl_ext {g h : G1 F} (e : g.1 = h.1) : g = h := Subtype.ext e

private lemma sl_of {g h : G1 F} {p q r s : A F} (e : h.1 = !![p, q; r, s])
    (h00 : g.1 0 0 = p) (h01 : g.1 0 1 = q) (h10 : g.1 1 0 = r) (h11 : g.1 1 1 = s) : g = h := by
  apply sl_ext
  rw [e, Matrix.eta_fin_two g.1, h00, h01, h10, h11]

private lemma det_eq (g : G1 F) : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

private lemma nm_val (b : A F) (a : (A F)ˣ) :
    (nU b * mD a).1 = !![(a : A F), b * ((a⁻¹ : (A F)ˣ) : A F); 0, ((a⁻¹ : (A F)ˣ) : A F)] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, nU_val, mD_val, Matrix.mul_fin_two]
  simp

private lemma cell_val (b b' : A F) (a : (A F)ˣ) :
    (nU b * mD a * wW F * nU b').1 =
      !![-(b * ((a⁻¹ : (A F)ˣ) : A F)), (a : A F) - b * ((a⁻¹ : (A F)ˣ) : A F) * b';
        -((a⁻¹ : (A F)ˣ) : A F), -(((a⁻¹ : (A F)ˣ) : A F) * b')] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, nm_val, wW_val, nU_val,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  congr 1
  simp
  ring_nf

private lemma rel_part : Rel (nU (F := F)) mD (wW F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Group.isUnit _⟩
  · apply sl_ext
    simp [nU_val, Matrix.one_fin_two]
  · intro b c
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, nU_val, nU_val, nU_val, Matrix.mul_fin_two]
    simp [add_comm]
  · apply sl_ext
    simp [mD_val, Matrix.one_fin_two]
  · intro a a'
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, mD_val, mD_val, mD_val, Matrix.mul_fin_two]
    simp [mul_comm]
  · intro a b
    apply sl_ext
    have he : (a : A F) * ((a⁻¹ : (A F)ˣ) : A F) = 1 := a.mul_inv
    rw [Matrix.SpecialLinearGroup.coe_mul, nm_val, mD_val, nU_val, Matrix.mul_fin_two]
    have hq : (a : A F) ^ 2 * b * ((a⁻¹ : (A F)ˣ) : A F) = (a : A F) * b := by
      linear_combination ((a : A F) * b) * he
    simp [hq]
  · intro a
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, wW_val, mD_val, mD_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp

private lemma gauss_part : Gauss (nU (F := F)) mD (wW F) := by
  intro t
  apply sl_ext
  have he : (t : A F) * ((t⁻¹ : (A F)ˣ) : A F) = 1 := t.mul_inv
  rw [cell_val, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, wW_val, nU_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp [he]

private lemma tri_part (g : G1 F) : g 1 0 = 0 ↔ ∃ b a, g = nU b * mD a := by
  constructor
  · intro h
    have h' : g.1 1 0 = 0 := h
    have hd := det_eq g
    rw [h', mul_zero, sub_zero] at hd
    have hd' : g.1 1 1 * g.1 0 0 = 1 := by rw [mul_comm]; exact hd
    refine ⟨g.1 0 1 * g.1 0 0, ⟨g.1 0 0, g.1 1 1, hd, hd'⟩, ?_⟩
    refine sl_of (nm_val _ _) rfl ?_ h' rfl
    show g.1 0 1 = g.1 0 1 * g.1 0 0 * g.1 1 1
    linear_combination (-g.1 0 1) * hd
  · rintro ⟨b, a, rfl⟩
    show (nU b * mD a).1 1 0 = 0
    rw [nm_val]
    simp

private lemma tri_uniq (b b' : A F) (a a' : (A F)ˣ) (e : nU b * mD a = nU b' * mD a') : b = b' ∧ a = a' := by
  have h := congrArg Subtype.val e
  rw [nm_val, nm_val] at h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp at h00 h01
  have ha : a = a' := Units.ext h00
  subst ha
  exact ⟨(Units.mul_left_inj _).1 h01, rfl⟩

private lemma cell_part (g : G1 F) : IsUnit (g 1 0) ↔ ∃ b a b', g = nU b * mD a * wW F * nU b' := by
  constructor
  · rintro ⟨c, hc⟩
    have hc' : g.1 1 0 = (c : A F) := hc.symm
    have he : (c : A F) * ((c⁻¹ : (A F)ˣ) : A F) = 1 := c.mul_inv
    have hd := det_eq g
    rw [hc'] at hd
    refine ⟨g.1 0 0 * ((c⁻¹ : (A F)ˣ) : A F), -c⁻¹, g.1 1 1 * ((c⁻¹ : (A F)ˣ) : A F), ?_⟩
    refine sl_of (cell_val _ _ _) ?_ ?_ ?_ ?_
    · simp only [inv_neg, inv_inv, Units.val_neg]
      linear_combination (-g.1 0 0) * he
    · simp only [inv_neg, inv_inv, Units.val_neg]
      linear_combination (-((c : A F) * ((c⁻¹ : (A F)ˣ) : A F) ^ 2)) * hd +
        (-((c⁻¹ : (A F)ˣ) : A F) - g.1 0 1 * ((c : A F) * ((c⁻¹ : (A F)ˣ) : A F) + 1)) * he
    · simp only [inv_neg, inv_inv, Units.val_neg, neg_neg]
      exact hc'
    · simp only [inv_neg, inv_inv, Units.val_neg]
      linear_combination (-g.1 1 1) * he
  · rintro ⟨b, a, b', rfl⟩
    show IsUnit ((nU b * mD a * wW F * nU b').1 1 0)
    rw [cell_val]
    simp
end

theorem UpperTheory.ConvolutionTheory.R2.C.grpRel :
    ∀ (F : Type) [Field F] [NumberField F], Rel (nU (F := F)) mD (wW F) ∧ Gauss (nU (F := F)) mD (wW F) ∧
    (∀ g : G1 F, g 1 0 = 0 ↔ ∃ b a, g = nU b * mD a) ∧ (∀ (b b' : A F) a a', nU b * mD a = nU b' * mD a' → b = b' ∧ a = a') ∧
    ∀ g : G1 F, IsUnit (g 1 0) ↔ ∃ b a b', g = nU b * mD a * wW F * nU b' := by
  intro F _ _
  exact ⟨rel_part, gauss_part, tri_part, tri_uniq, cell_part⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ImportsAlt
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.C

variable {F : Type} [Field F] [NumberField F]

def Dv (m : F) (x : A F) : Prop := ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (x.2 v) ≤ v.valuation F m

end UpperTheory.ConvolutionTheory.R2.C

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.LamGen
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.lamGen :
    (∀ (G H : Type) [Add G] [Add H] [MeasurableSpace G] [MeasurableSpace H] (μ : Measure G) (ν : Measure H) [SFinite μ] [SFinite ν] (γ φ : G → ℂ) (γ' φ' : H → ℂ),
      abelian₂ (μ.prod ν) (fun p => γ p.1 * γ' p.2) (fun p => φ p.1 * φ' p.2) = abelian₂ μ γ φ * abelian₂ ν γ' φ') ∧
    (∀ (ι G : Type) [Fintype ι] [Add G] [MeasurableSpace G] (μ : Measure G) [SigmaFinite μ] (γ φ : ι → G → ℂ),
      abelian₂ (Measure.pi fun _ : ι => μ) (fun v => ∏ i, γ i (v i)) (fun v => ∏ i, φ i (v i)) = ∏ i, abelian₂ μ (γ i) (φ i)) ∧
    ∀ (G H : Type) [Add G] [Add H] [MeasurableSpace G] [MeasurableSpace H] (μ : Measure G) (ν : Measure H) (e : G ≃ᵐ H) (c : ENNReal),
      (∀ x y, e (x + y) = e x + e y) → μ.map e = c • ν → ∀ γ φ : H → ℂ,
      abelian₂ μ (fun x => γ (e x)) (fun x => φ (e x)) = ((c.toReal : ℝ) : ℂ) ^ 2 * abelian₂ ν γ φ ∧ ∫ x, φ (e x) ∂μ = ((c.toReal : ℝ) : ℂ) * ∫ x, φ x ∂ν := by
  refine ⟨fun G H _ _ _ _ μ ν _ _ γ φ γ' φ' => ?_, fun ι G _ _ _ μ _ γ φ => ?_, fun G H _ _ _ _ μ ν e c he hm γ φ => ?_⟩
  · simp only [abelian₂]
    rw [← integral_prod_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [← integral_prod_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  · simp only [abelian₂]
    rw [← integral_fintype_prod_eq_prod]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [← integral_fintype_prod_eq_prod (fun i x => φ i x * γ i (x + y i))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Finset.prod_mul_distrib]
  · have key : ∀ u : H → ℂ, ∫ x, u (e x) ∂μ = ((c.toReal : ℝ) : ℂ) * ∫ x, u x ∂ν := fun u => by
      rw [← integral_map_equiv e u, hm, integral_smul_measure, Complex.real_smul]
    refine ⟨?_, key φ⟩
    simp only [abelian₂, he]
    have h1 : ∀ y, ∫ x, φ (e x) * γ (e x + e y) ∂μ = ((c.toReal : ℝ) : ℂ) * ∫ x, φ x * γ (x + e y) ∂ν := fun y =>
      key fun x => φ x * γ (x + e y)
    simp only [h1]
    rw [integral_const_mul, key fun y => ∫ x, φ x * γ (x + y) ∂ν]
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.MeasScale
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.measScale :
    ∀ (F : Type) [Field F] [NumberField F] (a : (A F)ˣ) (f : V4 F → ℂ), ∫ v, f (fun i => (a : A F) * v i) ∂(adeleMeasurePi F) = (((ab a)⁻¹ ^ 4 : ℝ) : ℂ) * ∫ v, f v ∂(adeleMeasurePi F) := by
  intro F _ _ a f
  have hpos : 0 ≤ ((IdeleGroup.ideleModule F a : ℝ))⁻¹ := inv_nonneg.mpr (IdeleGroup.ideleModule F a).2.le
  have hmap := GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_diagonal (K := F) (n := 4) (fun _ => a)
  have hf : (fun x : V4 F => x ᵥ* Matrix.diagonal (fun _ : Fin 4 => ((a : (A F)ˣ) : A F))) =
      fun x i => (a : A F) * x i := by
    funext x i
    rw [vecMul_diagonal, mul_comm]
  let e : V4 F ≃ᵐ V4 F := MeasurableEquiv.piCongrRight fun _ => (Homeomorph.smul a).toMeasurableEquiv
  have he : (e : V4 F → V4 F) = fun x i => (a : A F) * x i := rfl
  have h1 : ∫ v, f (fun i => (a : A F) * v i) ∂(adeleMeasurePi F) =
      ∫ v, f v ∂((adeleMeasurePi F).map (fun x : V4 F => fun i => (a : A F) * x i)) := by
    rw [← he]
    exact (e.measurableEmbedding.integral_map f).symm
  rw [h1, ← hf, hmap, integral_smul_measure, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow hpos, ENNReal.toReal_ofReal (pow_nonneg hpos 4), Complex.real_smul]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NormForm
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.normForm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (a : (A F)ˣ), (∃ s t : A F, (a : A F) = s ^ 2 - rt D.δ * t ^ 2) ↔ ∃ z : (A E)ˣ, ideleNorm F E z = a := by
  intro F E _ _ _ _ _ D a
  constructor
  · rintro ⟨s, t, h⟩
    have hm : D.mkE s t * D.bar (D.mkE s t) = am E (a : A F) := by rw [D.mkE_mul_bar, h]
    have hu : IsUnit (D.mkE s t * D.bar (D.mkE s t)) := by
      rw [hm]
      exact a.isUnit.map (am (F := F) E)
    obtain ⟨z, hz⟩ := isUnit_of_mul_isUnit_left hu
    refine ⟨z, Units.ext ?_⟩
    rw [D.coe_ideleNorm, hz, D.co_mkE, h]
    simp
  · rintro ⟨z, rfl⟩
    exact ⟨D.co z 0, D.co z 1, D.coe_ideleNorm z⟩
end

