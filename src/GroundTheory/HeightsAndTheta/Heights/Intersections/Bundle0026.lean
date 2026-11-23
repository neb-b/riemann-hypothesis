module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogIdealChain
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsUnitOfNumMem
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0024

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace PointVertical

section Reduction

variable {K : Type} {ι : K → Type} (p : ℕ)

abbrev red : MRing ι →+* MRingOver (ZMod p) ι := MvPolynomial.map (Int.castRingHom (ZMod p))

theorem red_surjective : Function.Surjective (red (ι := ι) p) :=
  MvPolynomial.map_surjective _ (fun x => ZMod.intCast_surjective x)

theorem ker_red_le {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) :
    RingHom.ker (red (ι := ι) p) ≤ J := by
  rw [MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton, Ideal.span_le,
    Set.singleton_subset_iff]
  simpa using hp

theorem mem_map_red_iff {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) (g : MRing ι) :
    red p g ∈ J.map (red p) ↔ g ∈ J := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ (red_surjective p), sup_eq_left.mpr]
  rw [← RingHom.ker_eq_comap_bot]
  exact ker_red_le p hp

theorem ringKrullDim_red {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) :
    ringKrullDim (MRingOver (ZMod p) ι ⧸ J.map (red p)) = ringKrullDim (MRing ι ⧸ J) := by
  have e : J = RingHom.ker ((Ideal.Quotient.mk (J.map (red p))).comp (red p)) := by
    ext g
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, mem_map_red_iff p hp]
  exact (ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq e).trans
    (RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp (red_surjective p))))).symm

theorem isMultiProjPrime_red [∀ k, Fintype (ι k)] {J : Ideal (MRing ι)} (hJ : IsMultiProjPrime J)
    (hp : ((p : ℕ) : MRing ι) ∈ J) : IsMultiProjPrime (J.map (red p)) := by
  obtain ⟨hJp, ⟨S, hS, hJS⟩, hJr⟩ := hJ
  refine ⟨Ideal.map_isPrime_of_surjective (red_surjective p) (ker_red_le p hp),
    ⟨red p '' S, ?_, by rw [hJS, Ideal.map_span]⟩, fun k => ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm => ha m (support_map_subset _ _ hm)⟩
  · obtain ⟨i, hi⟩ := hJr k
    refine ⟨i, fun h => hi ((mem_map_red_iff p hp _).mp ?_)⟩
    rw [map_X]
    exact h

variable {K' : Type} {ι' : K' → Type}

theorem imageVar_red [Fact p.Prime] (v : (Σ k, ι k) → (Σ k', ι' k')) {W : Ideal (MRing ι')}
    (hp : ((p : ℕ) : MRing ι') ∈ W) :
    imageVar (ZMod p) v (W.map (red p)) = (imageZ v W).map (red p) := by
  have hp' : ((p : ℕ) : MRing ι) ∈ imageZ v W := by
    show rename v ((p : ℕ) : MRing ι) ∈ W
    simpa using hp
  ext f
  obtain ⟨g, rfl⟩ := red_surjective p f
  rw [mem_map_red_iff p hp' g]
  show rename v (red p g) ∈ W.map (red p) ↔ rename v g ∈ W
  rw [← map_rename, mem_map_red_iff p hp]

theorem isMultiHomog_rename [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {t : MRing ι} {a : K → ℕ} (ht : IsMultiHomog t a) :
    IsMultiHomog (rename v t) (Function.extend κ a 0) := by
  classical
  have ht' := (Bridge.isMultiHomog_iff t a).mpr ht
  refine (Bridge.isMultiHomog_iff _ _).mp ?_
  have e := FieldNumbers.ContractRelevant.rename_weightedHomogeneousComponent hv.2.2.1 hv.1 hv.2.1 a t
  rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same ht'] at e
  rw [e]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem isMultiProjPrime_imageZ [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {W : Ideal (MRing ι')} (hW : IsMultiProjPrime W) : IsMultiProjPrime (imageZ v W) := by
  classical
  have h := FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (R := ℤ) hv.2.2.1 hv.1 hv.2.1
    (fun w hw => hv.2.2.2 w hw) ((Bridge.isMultiProjPrime_iff W).mpr hW)
  exact (Bridge.isMultiProjPrime_iff _).mp h

end Reduction

theorem exists_dim_F {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (p : ℕ) [Fact p.Prime]
    (V : Ideal (MRingOver (ZMod p) ι)) (hV : IsMultiProjPrime V) :
    ∃ D : ℕ, Fintype.card K ≤ D ∧ ringKrullDim (MRingOver (ZMod p) ι ⧸ V) = D := by
  classical
  have := hV.1
  have hmh := (Bridge.isMultiHomogIdeal_iff V).mpr hV.2.1
  exact FieldNumbers.PFContracted.exists_ringKrullDim_eq
    (fun T q hq => FieldNumbers.PFContracted.killBlocks_mem_of_isMultiHomogIdeal hmh T hq) hV.2.2

theorem geoNum_eq_zero
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hPC : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], ProjContractStatement F ι ι')
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d n : ℕ}
    (hP : IsArithVar (imageZ v P') d) (hdn : d < n + 1) {W : Ideal (MRing ι')} (hPW : P' ≤ W)
    (hWm : IsMultiProjPrime W) (hpr : (charOf W).Prime)
    (hWd : ringKrullDim (MRing ι' ⧸ W) = ((n + Fintype.card K' : ℕ) : WithBot ℕ∞)) (L : Fin n → K → ℤ) :
    geoNum n W (fun j => pullDeg κ (L j)) = 0 := by
  set p := charOf W with hpdef
  have : Fact p.Prime := ⟨hpr⟩
  have hpW : ((p : ℕ) : MRing ι') ∈ W := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W
  have hWp : IsProjVarF (W.map (red p)) n := ⟨isMultiProjPrime_red p hWm hpW, by rw [ringKrullDim_red p hpW, hWd]⟩
  have hImm : IsMultiProjPrime (imageZ v W) := isMultiProjPrime_imageZ hv hWm
  have hpI : ((p : ℕ) : MRing ι) ∈ imageZ v W := by
    show rename v ((p : ℕ) : MRing ι) ∈ W
    simpa using hpW
  have hVm := isMultiProjPrime_red p hImm hpI
  obtain ⟨D, hKD, hD⟩ := exists_dim_F p _ hVm
  obtain ⟨-, ⟨hQp, -, -⟩, hQh, hQd⟩ := hP
  have := hQp
  have hle : imageZ v P' ≤ imageZ v W := Ideal.comap_mono hPW
  have hpQ : ((p : ℕ) : MRing ι) ∉ imageZ v P' := by
    intro h
    have h2 : ((p : ℕ) : ℤ) ∈ (imageZ v P').comap (C : ℤ →+* MRing ι) := by
      rw [Ideal.mem_comap, map_natCast]
      exact h
    rw [hQh, Ideal.mem_bot] at h2
    exact hpr.ne_zero (by exact_mod_cast h2)
  have hdim := krullDim_quot_add_one_le hle hpI hpQ
  rw [← ringKrullDim_red p hpI, hD, hQd] at hdim
  have hD' : D + 1 ≤ d + Fintype.card K := by exact_mod_cast hdim
  have hVi : IsProjVarF (imageVar (ZMod p) v (W.map (red p))) (D - Fintype.card K) := by
    rw [imageVar_red p v hpW]
    refine ⟨hVm, ?_⟩
    rw [hD, Nat.sub_add_cancel hKD]
  obtain ⟨I, hI, -⟩ := hR4 (ZMod p) K' ι'
  rw [hGeo K' ι' p I hI W n _ hWm hpW hWp]
  exact hPC (ZMod p) K ι K' ι' I hI κ v _ n _ L hv hWp hVi (by omega)

end PointVertical


open PointVertical in
theorem ProjectivePointVertical.proof
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hPC : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], ProjContractStatement F ι ι') :
    ProjectivePointVertical.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d n L L' t a hv hP' hP hdn hL ht htQ
  classical
  have hs : IsSectionOn P' (HermLine.sqMetric (ι := ι') (Function.extend κ a 0)) (rename v t) :=
    ⟨Function.extend κ a 0, fun _ => rfl, isMultiHomog_rename hv ht, htQ⟩
  unfold vertR
  refine finsum_mem_eq_zero_of_forall_eq_zero fun W hW => ?_
  obtain ⟨-, hvert⟩ := divSuppArith K' ι' P' n _ _ W hP' hs hW
  by_cases hh : IsHorizontal W
  · simp [hh]
  · obtain ⟨hWm, hpr, hWd⟩ := hvert hh
    have hPW : P' ≤ W := le_sup_left.trans hW.1.1.2
    have e : (fun j => (L' j).a) = fun j => pullDeg κ (L j).a := funext fun j => (hL j).1
    simp only [if_neg hh, e, geoNum_eq_zero hGeo hR4 hPC hv hP hdn hPW hWm hpr hWd (fun j => (L j).a)]
    simp

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.OrderOfIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

theorem RegularityOrder.order_of_integral {F : Type*} [Field F] [NumberField F] (S : Subring F)
    (hint : ∀ x ∈ S, IsIntegral ℤ x) (hden : ∀ x : F, ∃ c ∈ S, c ≠ 0 ∧ x * c ∈ S) :
    Module.Finite ℤ S ∧ Module.Free ℤ S ∧ Module.finrank ℤ S = Module.finrank ℚ F := by

  have hmul : ∀ x : F, ∃ m : ℤ, m ≠ 0 ∧ (m : F) * x ∈ S := by
    intro x
    obtain ⟨c, hc, hc0, hxc⟩ := hden x
    have hci : IsIntegral ℤ (⟨c, hc⟩ : S) :=
      (isIntegral_algHom_iff S.subtype.toIntAlgHom Subtype.val_injective).1 (hint c hc)
    have hne := Ideal.comap_ne_bot_of_integral_mem (I := Ideal.span {(⟨c, hc⟩ : S)})
      (fun h => hc0 (congrArg Subtype.val h)) (Ideal.mem_span_singleton_self _) hci
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hm)
    refine ⟨m, hm0, ?_⟩
    have hmdc : (m : F) = (d : F) * c := by
      have := congrArg Subtype.val hd
      simpa using this.symm
    rw [hmdc, mul_assoc, mul_comm c x]
    exact S.mul_mem d.2 hxc

  let φ : S →ₗ[ℤ] 𝓞 F :=
    { toFun := fun x => ⟨x, hint x x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := fun x y h =>
    Subtype.ext (congrArg (fun z : 𝓞 F => (z : F)) h)
  have : Module.Finite ℤ S := Module.Finite.of_injective φ hφ
  have : Module.IsTorsionFree ℤ S := hφ.moduleIsTorsionFree φ (fun r x => φ.map_smul r x)
  have : Module.Free ℤ S := Module.free_of_finite_type_torsion_free'
  refine ⟨inferInstance, inferInstance, le_antisymm ?_ ?_⟩
  · rw [← RingOfIntegers.rank]
    exact LinearMap.finrank_le_finrank_of_injective hφ
  · rw [← RingOfIntegers.rank]
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 F)
    choose m hm0 hmS using fun i => hmul (s i : F)
    have hM0 : (∏ i, m i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hm0 i
    have hMS : ∀ y : 𝓞 F, ((∏ i, m i : ℤ) : F) * y ∈ S := by
      intro y
      have hy : y ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        obtain ⟨q, hq⟩ : m i ∣ ∏ j, m j := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
        rw [hq, Int.cast_mul, mul_comm (m i : F), mul_assoc]
        exact S.mul_mem (intCast_mem S q) (hmS i)
      | zero => simp
      | add y z _ _ hy hz =>
        convert S.add_mem hy hz using 1
        push_cast
        ring
      | smul r y _ hy =>
        convert S.zsmul_mem hy r using 1
        simp only [RingOfIntegers.coe_eq_algebraMap, zsmul_eq_mul, map_mul, map_intCast]
        ring
    let ψ : 𝓞 F →ₗ[ℤ] S :=
      { toFun := fun y => ⟨((∏ i, m i : ℤ) : F) * y, hMS y⟩
        map_add' := fun y z => Subtype.ext (by push_cast; ring)
        map_smul' := fun r y => Subtype.ext (by
          simp only [RingOfIntegers.coe_eq_algebraMap, zsmul_eq_mul, map_mul, map_intCast,
            Subring.coe_mul, SubringClass.coe_intCast, RingHom.id_apply]
          ring) }
    have hψ : Function.Injective ψ := by
      intro y z h
      have h' : ((∏ i, m i : ℤ) : F) * y = ((∏ i, m i : ℤ) : F) * z := congrArg Subtype.val h
      exact RingOfIntegers.eq_iff.1 (mul_left_cancel₀ (Int.cast_ne_zero.2 hM0) h')
    exact LinearMap.finrank_le_finrank_of_injective hψ

theorem RegularityOrder.proof (h₁ : RegularityFunctionFieldNumber.Statement) (h₂ : RegularityDenominator.Statement)
    (h₃ : RegularityIntegral.Statement) : RegularityOrder.Statement := by
  intro K _ ι _ P hP
  let f : funField P →ₐ[ℤ] FractionRing (MRing ι ⧸ P) :=
    { (funField P).subtype with commutes' := fun r => by simp }
  have hint₀ : ∀ x ∈ regRing P, IsIntegral ℤ x := fun x hx =>
    (isIntegral_algHom_iff f Subtype.val_injective).1 (h₃ K ι P hP ⟨x, hx⟩)
  obtain ⟨hF, hN⟩ := h₁ K ι P hP
  let _ : Field (funField P) := hF.toField
  have := hN
  have hint : ∀ x ∈ regRing P, IsIntegral ℤ x := hint₀
  have hden : ∀ x : funField P, ∃ c ∈ regRing P, c ≠ 0 ∧ x * c ∈ regRing P := by
    intro x
    obtain ⟨c, hc0, hc⟩ := h₂ K ι P x hP
    exact ⟨c, fun W h1 h2 => (hc W h1 h2).1, hc0, fun W h1 h2 => (hc W h1 h2).2⟩
  obtain ⟨hfin, hfree, hrank⟩ := RegularityOrder.order_of_integral (F := funField P) (regRing P) hint hden
  exact ⟨hfree, hfin, fun _ _ => hrank⟩

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagPivotIdentity
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

namespace FlagPivotIdentity

variable {R : Type} [CommRing R] {n : ℕ}

def leadDet (M : Matrix (Fin n) (Fin n) R) (k : ℕ) : R :=
  if h : k ≤ n then (M.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0

def pivotCof (M : Matrix (Fin n) (Fin n) R) {a : ℕ} (ha : a + 1 ≤ n) (i : Fin (a + 1)) : R :=
  (-1) ^ ((i : ℕ) + a) * (M.submatrix (Fin.castLE ha ∘ i.succAbove) (Fin.castLE (by omega))).det

theorem pivotMinor_eq_sum (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) (b : Fin n) :
    pivotMinor M a b = ∑ i : Fin (a + 1),
      pivotCof M (a := a) (by have := a.2; omega) i * M (Fin.castLE (by have := a.2; omega) i) b := by
  unfold pivotMinor
  rw [Matrix.det_succ_column _ (Fin.last a)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcol : pivotCols a b ∘ (Fin.last (a : ℕ)).succAbove = Fin.castLE (by have := a.2; omega) := by
    funext c
    rw [Fin.succAbove_last]
    ext
    simp [pivotCols]
  have hlast : pivotCols a b (Fin.last a) = b := by simp [pivotCols]
  simp only [pivotCof, Matrix.submatrix_apply, Matrix.submatrix_submatrix, Fin.val_last, hlast, hcol]
  ring

def pivotCoeff (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) : Matrix (Fin (j + 1)) (Fin (j + 1)) R :=
  Matrix.of fun a i =>
    if h : (i : ℕ) ≤ a then pivotCof M (a := a) (by have := j.2; have := a.2; omega) ⟨i, by omega⟩ else 0

theorem sum_castLE {m k : ℕ} (h : k ≤ m) (f : Fin m → R) (hf : ∀ i : Fin m, k ≤ (i : ℕ) → f i = 0) :
    ∑ i : Fin k, f (Fin.castLE h i) = ∑ i : Fin m, f i := by
  have e : ∑ i : Fin k, f (Fin.castLE h i) = ∑ i ∈ Finset.univ.map (Fin.castLEEmb h), f i := by
    rw [Finset.sum_map]; rfl
  rw [e]
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hf i ?_
  by_contra hlt
  push Not at hlt
  exact hi (Finset.mem_map.2 ⟨⟨i, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem pivotMatrix_rows (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) {m : ℕ} (e : Fin m → Fin n) :
    (pivotMatrix M).submatrix (Fin.castLE (n := (j : ℕ) + 1) (by have := j.2; omega)) e =
      pivotCoeff M j * M.submatrix (Fin.castLE (n := (j : ℕ) + 1) (by have := j.2; omega)) e := by
  ext a b
  have ha : (a : ℕ) < n - 1 := by have := j.2; have := a.2; omega
  rw [Matrix.mul_apply]
  simp only [Matrix.submatrix_apply, pivotMatrix, Matrix.of_apply, Fin.val_castLE, dif_pos ha]
  rw [pivotMinor_eq_sum M ⟨a, ha⟩ (e b)]
  rw [← sum_castLE (m := (j : ℕ) + 1) (k := (a : ℕ) + 1) (Nat.succ_le_of_lt a.2)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi : ((Fin.castLE (n := (a : ℕ) + 1) (m := (j : ℕ) + 1) (Nat.succ_le_of_lt a.2) i) : ℕ) ≤ a :=
      Nat.lt_succ_iff.mp i.2
    simp only [pivotCoeff, Matrix.of_apply]
    rw [dif_pos hi]
    rfl
  · intro i hi
    have : ¬ ((i : ℕ) ≤ a) := by omega
    simp only [pivotCoeff, Matrix.of_apply]
    rw [dif_neg this, zero_mul]

theorem pivotCoeff_isLowerTriangular (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) :
    (pivotCoeff M j).IsLowerTriangular := by
  intro a i hai
  have hai' : (a : ℕ) < i := OrderDual.toDual_lt_toDual.mp hai
  have : ¬ ((i : ℕ) ≤ a) := by omega
  simp only [pivotCoeff, Matrix.of_apply, dif_neg this]

theorem pivotCoeff_diag (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) (a : Fin (j + 1)) :
    pivotCoeff M j a a = leadDet M a := by
  have ha : (a : ℕ) ≤ n := by have := j.2; have := a.2; omega
  simp only [pivotCoeff, Matrix.of_apply, dif_pos le_rfl, pivotCof, leadDet, dif_pos ha]
  have hl : (⟨a, Nat.lt_succ_self _⟩ : Fin ((a : ℕ) + 1)) = Fin.last a := rfl
  rw [hl, Fin.succAbove_last, Even.neg_one_pow ⟨a, rfl⟩, one_mul]
  rfl

theorem leadMinor_eq (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) :
    leadMinor M a = leadDet M (a + 1) := by
  have h : (a : ℕ) + 1 ≤ n := by have := a.2; omega
  unfold leadMinor pivotMinor leadDet
  rw [dif_pos h]
  congr 2
  funext c
  rcases c with ⟨c, hc⟩
  ext
  simp only [pivotCols, Fin.castLE_mk]
  split_ifs <;> (simp; try omega)

theorem leadDet_zero (M : Matrix (Fin n) (Fin n) R) : leadDet M 0 = 1 := by
  simp [leadDet]

theorem proof : FlagPivotIdentity.Statement := by
  intro R _ n M j S
  have hP : flagMinor (pivotMatrix M) j S =
      (∏ k ∈ Finset.range j, leadDet M (k + 1)) * flagMinor M j S := by
    unfold flagMinor
    rw [pivotMatrix_rows, Matrix.det_mul,
      Matrix.det_of_isLowerTriangular _ (pivotCoeff_isLowerTriangular M j)]
    simp only [pivotCoeff_diag]
    rw [Fin.prod_univ_eq_prod_range (fun k => leadDet M k), Finset.prod_range_succ', leadDet_zero, mul_one]
  have hI : ∏ a ∈ Finset.Iic j, leadMinor M a = ∏ k ∈ Finset.range (j + 1), leadDet M (k + 1) := by
    simp only [leadMinor_eq]
    have e := Finset.prod_map (Finset.Iic j) Fin.valEmbedding (fun k => leadDet M (k + 1))
    rw [Fin.map_valEmbedding_Iic] at e
    rw [← show (Finset.Iic (j : ℕ)) = Finset.range (j + 1) by ext; simp, e]
    rfl
  rw [hP, hI, Finset.prod_range_succ, leadMinor_eq]
  ring

end FlagPivotIdentity

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ProofOfNoethPow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityLocalFinite.proof (hD : regularityLocalDimension_holds.Statement) : RegularityLocalFinite.Statement := by
  intro K _ ι _ P s a W y hP hs hsP hW hy hy0
  obtain ⟨hloc, hnoeth, hdim⟩ := hD K ι P s a W hP hs hsP hW
  have := hloc
  have := hnoeth
  have : P.IsPrime := hP.2.1.1
  have : IsDomain (locRing P W) := inferInstance
  have : Ring.KrullDimLE 1 (locRing P W) := ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq hdim
  have hfinRes : Finite (IsLocalRing.ResidueField (locRing P W)) :=
    (regularityLocalResidue_holds.proof K ι P s a W (fun i => i.elim0) hP hs hsP hW).1
  letI := hfinRes
  have hy0' : (⟨y, hy⟩ : locRing P W) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  have hfin : Module.length (locRing P W) (locRing P W ⧸ locIdeal P W y) ≠ ⊤ := by
    rw [locIdeal_eq_span hy, span_singleton_eq_range_lsmul]
    exact ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top (locRing P W) hy0'
  have hcard := card_eq_card_residueField_pow_length (locRing P W ⧸ locIdeal P W y) hfin
  have hpos : 0 < Nat.card (IsLocalRing.ResidueField (locRing P W)) := Nat.card_pos
  apply Nat.finite_of_card_ne_zero
  rw [hcard]
  exact pow_ne_zero _ hpos.ne'

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFVert
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFVert.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d r : ℕ)
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι')
    (s : MRing ι') (a : K' → ℕ) (W : Ideal (MRing ι')),
    IsBlockMap κ v → IsArithVar P' (d + r + 1) → IsArithVar (imageZ v P') d →
    (∀ j, IsPullHerm κ v (L j) (L' j)) → IsMultiHomog s a → s ∉ P' →
    W ∈ divSupp P' s → ¬ IsHorizontal W →
    geoNum (d + r) W (fun j => (Fin.append L' N j).a) = 0

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Inter
end

