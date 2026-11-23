module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalPowerSeriesOfAdelicIntegralPositiveRad
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RatCrit

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem hankel_pow_mul (a : F) (c : ℕ → F) (n : ℕ) :
    hankel (fun i => a ^ i * c i) n = a ^ (n * (n + 1)) * hankel c n := by
  have hM : (Matrix.of fun i j : Fin (n + 1) => a ^ ((i : ℕ) + j) * c (i + j)) =
      Matrix.diagonal (fun i : Fin (n + 1) => a ^ (i : ℕ)) * (Matrix.of fun i j : Fin (n + 1) => c (i + j)) *
        Matrix.diagonal (fun i : Fin (n + 1) => a ^ (i : ℕ)) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.of_apply, pow_add]
    ring
  unfold hankel
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  have hs : (∑ i : Fin (n + 1), (i : ℕ)) * 2 = n * (n + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i) (n + 1), Finset.sum_range_id_mul_two]
    simp [mul_comm]
  rw [← hs, pow_mul]
  ring

theorem ord_mul' (v : Place k F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord v (x * y) = ord v x + ord v y := by
  unfold ord
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]
  ring

theorem ord_pow' (v : Place k F) (x : F) (m : ℕ) : ord v (x ^ m) = m * ord v x := by
  unfold ord
  rw [map_pow, WithZero.log_pow, nsmul_eq_mul]
  ring

theorem ord_of_eq_one (v : Place k F) {x : F} (h : v.1 x = 1) : ord v x = 0 := by
  simp [ord, h]

end GlobalTheory.RatCrit

namespace GlobalTheory.RatCrit

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem ord_hankel_ge (v : Place k F) (φ : PowerSeries F) (u : F) (e ψ : PowerSeries v.O) (hu : u ≠ 0)
    (he0 : PowerSeries.constantCoeff e ≠ 0)
    (heq : sc v u e * φ = sc v u ψ) (n : ℕ) (hH : hankel (fun i => PowerSeries.coeff i φ) n ≠ 0) :
    ((n * (n + 1) : ℕ) : ℤ) * ord v u - ((2 * (n + 1) : ℕ) : ℤ) * ord v ((PowerSeries.constantCoeff e : v.O) : F) ≤
      ord v (hankel (fun i => PowerSeries.coeff i φ) n) := by
  have hr : ∀ f : PowerSeries F, PowerSeries.rescale u⁻¹ (PowerSeries.rescale u f) = f := by
    intro f; ext m
    simp only [PowerSeries.coeff_rescale, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hu, one_pow, one_mul]
  have h1 : PowerSeries.map v.O.subtype e * PowerSeries.rescale u⁻¹ φ = PowerSeries.map v.O.subtype ψ := by
    have := congrArg (PowerSeries.rescale u⁻¹) heq
    simpa only [sc, RingHom.comp_apply, map_mul, hr] using this
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.Nef.hankel_integral v.O F v.O.subtype e ψ (PowerSeries.rescale u⁻¹ φ) n h1
  have h2 : (fun i => PowerSeries.coeff i φ) = fun i => u ^ i * PowerSeries.coeff i (PowerSeries.rescale u⁻¹ φ) := by
    funext i
    rw [PowerSeries.coeff_rescale, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hu, one_pow, one_mul]
  set c : F := ((PowerSeries.constantCoeff e : v.O) : F) with hc
  set H := hankel (fun i => PowerSeries.coeff i φ) n with hHdef
  set H0 := hankel (fun i => PowerSeries.coeff i (PowerSeries.rescale u⁻¹ φ)) n with hH0
  have h3 : H = u ^ (n * (n + 1)) * H0 := by rw [hHdef, h2, hankel_pow_mul]
  have hz' : (z : F) = c ^ (2 * (n + 1)) * H0 := hz
  have h4 : c ^ (2 * (n + 1)) * H = u ^ (n * (n + 1)) * (z : F) := by rw [h3, hz']; ring
  have hH0 : H0 ≠ 0 := by
    intro h; exact hH (by rw [h3, h, mul_zero])
  have hcne : c ≠ 0 := by
    intro h; apply he0; ext; simpa [hc] using h
  have hzne : (z : F) ≠ 0 := by rw [hz']; exact mul_ne_zero (pow_ne_zero _ hcne) hH0
  have hz1 : 0 ≤ ord v (z : F) :=
    ((_root_.GlobalTheory.Nef.ord_calculus k F v).2.2.1 _ hzne).1 ((Valuation.mem_valuationSubring_iff _ _).1 z.2)
  have h5 := congrArg (ord v) h4
  rw [ord_mul' v (pow_ne_zero _ hcne) hH, ord_mul' v (pow_ne_zero _ hu) hzne, ord_pow', ord_pow'] at h5
  linarith

end GlobalTheory.RatCrit

namespace GlobalTheory.RatCrit

theorem isRat_of_adelic : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (φ : PowerSeries F) (u : Place k F → F) (e ψ : ∀ v : Place k F, PowerSeries v.O), (∀ v, u v ≠ 0) → {v | ord v (u v) ≠ 0}.Finite → 0 < ∑ᶠ v, ord v (u v) → (∀ v, PowerSeries.constantCoeff (e v) ≠ 0) → {v | ¬ IsUnit (PowerSeries.constantCoeff (e v))}.Finite → (∀ v, sc v (u v) (e v) * φ = sc v (u v) (ψ v)) → IsRat φ := by
  intro k F _ _ _ _ _ hFF φ u e ψ hu0 hufin hdeg he0 hefin heq
  classical
  set c : Place k F → F := fun v => ((PowerSeries.constantCoeff (e v) : v.O) : F) with hc
  have hcunit : ∀ v, IsUnit (PowerSeries.constantCoeff (e v)) → v.1 (c v) = 1 := by
    intro v h
    obtain ⟨a, ha⟩ := h
    have h1 := ValuationSubring.valuation_unit v.O a
    rw [ha] at h1
    exact (Valuation.isEquiv_valuation_valuationSubring v.1).eq_one_iff_eq_one.2 h1
  set δ := ∑ᶠ v, ord v (c v) with hδ
  set D := ∑ᶠ v, ord v (u v) with hD
  apply _root_.GlobalTheory.Nef.isRat_of_hankel_eventually_zero F φ ((2 * δ).toNat + 1)
  intro n hn
  by_contra hH
  obtain ⟨hHfin, hHsum⟩ := _root_.GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero k F hFF _ hH
  set H := hankel (fun i => PowerSeries.coeff i φ) n with hHdef
  let T : Finset (Place k F) := hufin.toFinset ∪ hefin.toFinset ∪ hHfin.toFinset
  have sU : Function.support (fun v => ord v (u v)) ⊆ (T : Set (Place k F)) := by
    intro v hv
    simp only [T, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl (Or.inl hv)
  have sC : Function.support (fun v => ord v (c v)) ⊆ (T : Set (Place k F)) := by
    intro v hv
    simp only [T, Finset.coe_union, Set.Finite.coe_toFinset]
    refine Or.inl (Or.inr ?_)
    intro h
    exact hv (ord_of_eq_one v (hcunit v h))
  have sH : Function.support (fun v => ord v H) ⊆ (T : Set (Place k F)) := by
    intro v hv
    simp only [T, Finset.coe_union, Set.Finite.coe_toFinset]
    refine Or.inr ?_
    intro h
    exact hv (ord_of_eq_one v h)
  rw [finsum_eq_sum_of_support_subset _ sH] at hHsum
  rw [finsum_eq_sum_of_support_subset _ sC] at hδ
  rw [finsum_eq_sum_of_support_subset _ sU] at hD
  have hsum : ∑ v ∈ T, (((n * (n + 1) : ℕ) : ℤ) * ord v (u v) - ((2 * (n + 1) : ℕ) : ℤ) * ord v (c v)) ≤
      ∑ v ∈ T, ord v H :=
    Finset.sum_le_sum fun v _ => ord_hankel_ge v φ (u v) (e v) (ψ v) (hu0 v) (he0 v) (heq v) n hH
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hD, ← hδ, hHsum] at hsum
  have hn' : 2 * δ + 1 ≤ (n : ℤ) := by
    have := Int.self_le_toNat (2 * δ)
    omega
  have hD1 : 1 ≤ D := hdeg
  push_cast at hsum
  have h6 : (n + 1 : ℤ) * (n * D - 2 * δ) ≤ 0 := by linarith [hsum]
  have h7 : (n : ℤ) * D - 2 * δ ≤ 0 := by
    by_contra h8
    push_neg at h8
    have : (0 : ℤ) < (n + 1 : ℤ) * (n * D - 2 * δ) := mul_pos (by positivity) h8
    linarith
  have h9 : (n : ℤ) ≤ n * D := by nlinarith [(Nat.cast_nonneg n : (0 : ℤ) ≤ n)]
  linarith

end GlobalTheory.RatCrit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSheafProjBundleCochainPresheafEtale
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.CotSheaf

open CupSpec

variable {R : Type} [CommRing R] {q N : ℕ} {I : Cx R} {n : ℤ}

def fstHom {U W : Scheme.{0}} {E : Spc} {p : ℕ} (y : Sx (sch.obj U ⨯ E) p W) : W ⟶ U := y.map prod.fst

theorem fstHom_pair {U W : Scheme.{0}} {E : Spc} {p : ℕ} (v : W ⟶ U) (b : Sx E p W) :
    fstHom (sxPair (schSx v p) b) = v := sxPair_fst _ _

theorem fstHom_res {U W W' : Scheme.{0}} {E : Spc} {p : ℕ} (y : Sx (sch.obj U ⨯ E) p W) (w : W' ⟶ W) :
    fstHom (y.res w) = w ≫ fstHom y := by
  rw [fstHom, sxMap_res]; rfl

theorem fstHom_map {U Y W : Scheme.{0}} {E : Spc} {p : ℕ} (y : Sx (sch.obj Y ⨯ E) p W) (g : Y ⟶ U) :
    fstHom (y.map (prod.map (sch.map g) (𝟙 E))) = fstHom y ≫ g := by
  rw [fstHom, ← sxMap_comp, prod.map_fst, sxMap_comp]; rfl

theorem snd_map {U Y W : Scheme.{0}} {E : Spc} {p : ℕ} (y : Sx (sch.obj Y ⨯ E) p W) (g : Y ⟶ U) :
    (y.map (prod.map (sch.map g) (𝟙 E))).map prod.snd = y.map prod.snd := by
  rw [← sxMap_comp, prod.map_snd, Category.comp_id]

theorem sx_res_res {E : Spc} {p : ℕ} {U V W : Scheme.{0}} (x : Sx E p U) (f : V ⟶ U) (g : W ⟶ V) :
    (x.res f).res g = x.res (g ≫ f) := by
  change _ = (E.obj (op (SimplexCategory.mk p))).map (g ≫ f).op x
  rw [op_comp, Functor.map_comp_apply]; rfl

theorem ev_res_pair {U W W' : Scheme.{0}} (α : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (y : Sx (sch.obj U ⨯ fibQ q N) p W) (w : W' ⟶ W) :
    Sec.res w (ev (R := R) α p s h W y) =
      ev (R := R) (I := I) (E := sch.obj W' ⨯ fibQ q N) (((cotPre R q N I n).map (w ≫ fstHom y).op).hom α) p s h W'
        (sxPair (schSx (𝟙 W') p) ((y.map prod.snd).res w)) := by
  have hres : Sec.res w (ev (R := R) α p s h W y) = ev (R := R) α p s h W' (y.res w) := by
    change Sec.res w (Sec.map ((chainsXIso R _ p).inv ≫ α.v _ _ h) (freeGen R _ W y)) = _
    rw [map_res, freeGen_res]
    rfl
  rw [hres]
  let f : sch.obj W' ⨯ fibQ q N ⟶ sch.obj U ⨯ fibQ q N :=
    prod.map (sch.map (w ≫ fstHom y)) (𝟙 _)
  let x := sxPair (schSx (𝟙 W') p) ((y.map prod.snd).res w)
  have hmap : ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h W' x =
      ev (R := R) α p s h W' (x.map f) := by
    unfold ev
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chains_map, Category.assoc]
    change Sec.map ((chainsXIso R _ p).inv ≫ α.v _ _ h)
      (Sec.map ((free R).map (f.app (op (SimplexCategory.mk p)))) (freeGen R _ W' x)) = _
    rw [freeGen_map]
    rfl
  change _ = ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h W' x
  rw [hmap]
  dsimp only [f, x]
  congr 1
  apply sx_prod_ext
  · rw [sxPair_map, sxPair_fst, sxMap_res, schSx_map, Category.id_comp]
    rfl
  · rw [sxMap_res, sxPair_map, sxPair_snd]
    rfl

end GlobalTheory.EtC.CotSheaf

namespace GlobalTheory.EtC

open CupSpec CotSheaf

theorem cotPre_isSheaf (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ) :
    Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R))), isSheaf_iff_isSheaf_of_type]
  have hI : ∀ s : ℤ, Presieve.IsSheaf Scheme.etaleTopology.{0} ((I.X s).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    fun s => (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 (I.X s).property)
  have sep : ∀ (s : ℤ) (W : Scheme.{0}) (T : Sieve W), T ∈ Scheme.etaleTopology.{0} W → ∀ t t' : Sec (I.X s) W,
      (∀ (W' : Scheme.{0}) (w : W' ⟶ W), T w → Sec.res w t = Sec.res w t') → t = t' :=
    fun s W T hT t t' ht => (hI s T hT).isSeparatedFor.ext fun _ w hw => ht _ w hw
  intro U S hS c hc
  rw [Presieve.compatible_iff_sieveCompatible] at hc
  have hC : ∀ {Y Z : Scheme.{0}} (f : Y ⟶ U) (g : Z ⟶ Y) (hf : S f),
      ((cotPre R q N I n).map g.op).hom (c f hf) = c (g ≫ f) (S.downward_closed hf g) := fun f g hf => (hc f g hf).symm

  have hcong : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {W : Scheme.{0}} (g g' : W ⟶ U) (hg : S g) (hg' : S g')
      (x x' : Sx (fibQ q N) p W), g = g' → x = x' →
      ev (R := R) (I := I) (E := sch.obj W ⨯ fibQ q N) (c g hg) p s h W (sxPair (schSx (𝟙 W) p) x) =
        ev (R := R) (I := I) (E := sch.obj W ⨯ fibQ q N) (c g' hg') p s h W (sxPair (schSx (𝟙 W) p) x') := by
    rintro p s h W g _ hg hg' x _ rfl rfl; rfl

  have hL : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {W W' : Scheme.{0}} (g : W ⟶ U) (hg : S g)
      (x : Sx (fibQ q N) p W) (t : W' ⟶ W),
      Sec.res t (ev (R := R) (I := I) (E := sch.obj W ⨯ fibQ q N) (c g hg) p s h W (sxPair (schSx (𝟙 W) p) x)) =
        ev (R := R) (I := I) (E := sch.obj W' ⨯ fibQ q N) (c (t ≫ g) (S.downward_closed hg t)) p s h W'
          (sxPair (schSx (𝟙 W') p) (x.res t)) := by
    intro p s h W W' g hg x t
    refine (ev_res_pair (c g hg) p s h _ t).trans ?_
    rw [fstHom_pair, Category.comp_id, hC, sxPair_snd]

  have hAm : ∀ γ : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n,
      (∀ {Y : Scheme.{0}} (g : Y ⟶ U) (hg : S g), ((cotPre R q N I n).map g.op).hom γ = c g hg) →
      ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {W W' : Scheme.{0}} (y : Sx (sch.obj U ⨯ fibQ q N) p W) (w : W' ⟶ W)
        (hw : S (w ≫ fstHom y)),
      Sec.res w (ev (R := R) γ p s h W y) = ev (R := R) (I := I) (E := sch.obj W' ⨯ fibQ q N) (c (w ≫ fstHom y) hw) p s h W'
          (sxPair (schSx (𝟙 W') p) ((y.map prod.snd).res w)) := by
    intro γ hγ p s h W W' y w hw
    refine (ev_res_pair γ p s h y w).trans ?_
    rw [hγ]

  have key : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) p W),
      ∃ t : Sec (I.X s) W, ∀ (W' : Scheme.{0}) (w : W' ⟶ W) (hw : S (w ≫ fstHom y)),
        Sec.res w t = ev (R := R) (I := I) (E := sch.obj W' ⨯ fibQ q N) (c (w ≫ fstHom y) hw) p s h W'
          (sxPair (schSx (𝟙 W') p) ((y.map prod.snd).res w)) := by
    intro p s h W y
    let fam : Presieve.FamilyOfElements ((I.X s).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R)))
        (S.pullback (fstHom y)).arrows := fun W' w hw =>
      ev (R := R) (I := I) (E := sch.obj W' ⨯ fibQ q N) (c (w ≫ fstHom y) hw) p s h W'
          (sxPair (schSx (𝟙 W') p) ((y.map prod.snd).res w))
    have hfam : fam.Compatible := by
      rw [Presieve.compatible_iff_sieveCompatible]
      intro Y Z f g hf
      refine Eq.trans ?_ (hL p s h (f ≫ fstHom y) hf _ g).symm
      exact hcong _ _ _ _ _ _ _ _ _ (Category.assoc _ _ _) (sx_res_res _ _ _).symm
    obtain ⟨t, ht, -⟩ := hI s _ (Scheme.etaleTopology.{0}.pullback_stable (fstHom y) hS) fam hfam
    exact ⟨t, fun W' w hw => ht w hw⟩
  choose a ha using key
  have hnat : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (V W : Scheme.{0}) (g : V ⟶ W)
      (y : Sx (sch.obj U ⨯ fibQ q N) p W), Sec.res g (a p s h W y) = a p s h V (y.res g) := by
    intro p s h V W g y
    apply sep s V _ (Scheme.etaleTopology.{0}.pullback_stable (fstHom (y.res g)) hS)
    intro W' w hw
    have hw' : S ((w ≫ g) ≫ fstHom y) := by
      rw [fstHom_res] at hw; simpa [Category.assoc] using hw
    rw [secRes_res, ha p s h W y W' (w ≫ g) hw', ha p s h V (y.res g) W' w hw]
    refine hcong _ _ _ _ _ _ _ _ _ ?_ ?_
    · rw [fstHom_res, Category.assoc]
    · rw [sxMap_res, sx_res_res]
  let E := sch.obj U ⨯ fibQ q N
  have components : ∀ (i j : ℤ) (hij : i + n = j),
      ∃ φ : ((chains R).obj E).X i ⟶ I.X j, ∀ (p : ℕ) (hp : i = -(p : ℤ)) W y,
        Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ)
          (freeGen R _ W y) = a p j (hp ▸ hij) W y := by
    intro i j hij
    by_cases hi : i ≤ 0
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := free_exists (R := R) _ _ (a p j hij) (hnat p j hij)
      refine ⟨(chainsXIso R E p).hom ≫ φ, fun p' hp W y => ?_⟩
      obtain rfl : p = p' := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ W y
    · exact ⟨0, fun p hp => by omega⟩
  choose φ hφ using components
  let α : Cochain ((chains R).obj E) I n := Cochain.mk φ
  have hα : ∀ p s h W y, ev (R := R) α p s h W y = a p s h W y := by
    intro p s h W y
    have heval := hφ _ _ h p rfl W y
    rw [eqToHom_refl, Category.id_comp] at heval
    exact heval
  have hext {E' : Spc} (β γ : Cochain ((chains R).obj E') I n)
      (heval : ∀ p s h W y, ev (R := R) β p s h W y = ev (R := R) γ p s h W y) : β = γ := by
    ext i j hij : 1
    by_cases hi : i ≤ 0
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R E' p).inv]
      exact free_ext _ _ (fun W y => heval p j hij W y)
    · exact (isZero_chains E' i (by omega)).eq_of_src _ _
  have hαam : ∀ {Y : Scheme.{0}} (g : Y ⟶ U) (hg : S g), ((cotPre R q N I n).map g.op).hom α = c g hg := by
    intro Y g hg
    apply hext
    intro p s h W y
    let f : sch.obj Y ⨯ fibQ q N ⟶ E := prod.map (sch.map g) (𝟙 _)
    have hmap : ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h W y =
        ev (R := R) α p s h W (y.map f) := by
      unfold ev
      rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chains_map, Category.assoc]
      change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h)
        (Sec.map ((free R).map (f.app (op (SimplexCategory.mk p)))) (freeGen R _ W y)) = _
      rw [freeGen_map]
      rfl
    change ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h W y = _
    rw [hmap, hα]
    apply sep s W _ (Scheme.etaleTopology.{0}.pullback_stable (fstHom (y.map (prod.map (sch.map g) (𝟙 _)))) hS)
    intro W' w hw
    rw [ha p s h W _ W' w hw]
    refine Eq.trans ?_ (ev_res_pair (c g hg) p s h y w).symm
    rw [hC, snd_map]
    refine hcong _ _ _ _ _ _ _ _ _ ?_ rfl
    rw [fstHom_map, Category.assoc]
  refine ⟨α, fun Y g hg => hαam g hg, fun β hβ => ?_⟩
  apply hext
  intro p s h W y
  apply sep s W _ (Scheme.etaleTopology.{0}.pullback_stable (fstHom y) hS)
  intro W' w hw
  rw [hAm β (fun g hg => hβ g hg) p s h y w hw, hAm α (fun g hg => hαam g hg) p s h y w hw]

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTwoMulRhoSubTr
section
noncomputable section

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

open NumberField

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

theorem sq_two_mul_rho_sub_tr (b : Base D R) :
    (2 * b.ρ - (D.tr : R)) ^ 2 = ((D.tr ^ 2 - 4 * D.nm : ℤ) : R) := by
  have h := b.ρ_root
  push_cast
  linear_combination 4 * h

theorem isUnit_two_mul_rho_sub_tr (b : Base D R) : IsUnit (2 * b.ρ - (D.tr : R)) := by
  have hp : (p).Prime := Fact.out
  set d : ℤ := D.tr ^ 2 - 4 * D.nm with hd
  have hc : d.natAbs.Coprime p := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => D.disc_p ?_)
    exact Int.natCast_dvd.2 h
  have hu := b.unit _ hc
  have hdu : IsUnit ((d : ℤ) : R) := by
    rcases Int.natAbs_eq d with h | h
    · rw [h, Int.cast_natCast]; exact hu
    · rw [h, Int.cast_neg, Int.cast_natCast]; exact hu.neg
  rw [← sq_two_mul_rho_sub_tr] at hdu
  exact (isUnit_pow_iff two_ne_zero).1 hdu

def uInv (b : Base D R) : R := ↑(isUnit_two_mul_rho_sub_tr b).unit⁻¹

theorem uInv_mul (b : Base D R) : uInv b * (2 * b.ρ - (D.tr : R)) = 1 :=
  (isUnit_two_mul_rho_sub_tr b).val_inv_mul

def comaxC (b : Base D R) (i j : Fin D.a) : 𝓞 D.F →₀ R :=
  if h : i ≠ j then
    Classical.choose (Finsupp.mem_span_range_iff_exists_finsupp.1
      ((b.comax i j h).symm ▸ Submodule.mem_top :
        (1 : R) ∈ Ideal.span (Set.range fun x => b.t i x - b.t j x)))
  else 0

theorem comaxC_spec (b : Base D R) {i j : Fin D.a} (h : i ≠ j) :
    ((comaxC b i j).sum fun x r => r * (b.t i x - b.t j x)) = 1 := by
  unfold comaxC
  rw [dite_eq_left h]
  exact Classical.choose_spec (Finsupp.mem_span_range_iff_exists_finsupp.1
      ((b.comax i j h).symm ▸ Submodule.mem_top :
        (1 : R) ∈ Ideal.span (Set.range fun x => b.t i x - b.t j x)))

variable {B : Type} [CommRing B] {n : ℕ}

def alphaMat (b : Base D R) (βB : R →+* B) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (i j : Fin D.a) :
    Matrix (Fin n) (Fin n) B :=
  (comaxC b i j).sum fun x r =>
    algebraMap B (Matrix (Fin n) (Fin n) B) (βB r) * (M x - algebraMap B (Matrix (Fin n) (Fin n) B) (βB (b.t j x)))

def projMat (b : Base D R) (βB : R →+* B) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (i : Fin D.a) :
    Matrix (Fin n) (Fin n) B :=
  (List.ofFn fun j => if j = i then 1 else alphaMat b βB M i j).prod *
    (algebraMap B (Matrix (Fin n) (Fin n) B) (βB (uInv b)) *
      (M D.ω - algebraMap B (Matrix (Fin n) (Fin n) B) (βB ((D.tr : R) - b.ρ))))

end GlobalTheory.UPel.HT.LieLin.RankIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyTwoInstances
section
set_option autoImplicit false

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.JoinedTwoProof

universe a b

theorem main : JoinedTwo.{a, b} := by
  intro C _ C' _ K K' m m' θ j c
  obtain ⟨⟨⟨z, w, η⟩, hc⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨h1, h2, h3, -⟩ := hc
  dsimp only at h1 h2 h3
  refine QuotientAddGroup.eq.2 ⟨(fun T T' φ ↦ m'.a0 T' (z _ _ _ (θ.app T) (m'.G.map φ) - z _ _ _ (m.G.map φ) (θ.app T')),
    fun T ↦ m'.a1 T (w _ _ (θ.app T))), ?_⟩
  refine Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun T'' ↦ funext fun φ ↦ funext fun ψ ↦ ?_)
    (Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun φ ↦ ?_) (funext fun T ↦ ?_))
  · change K'.M0.map ψ (m'.a0 T' (z _ _ _ (θ.app T) (m'.G.map φ) - z _ _ _ (m.G.map φ) (θ.app T'))) -
        m'.a0 T'' (z _ _ _ (θ.app T) (m'.G.map (φ ≫ ψ)) - z _ _ _ (m.G.map (φ ≫ ψ)) (θ.app T'')) +
        m'.a0 T'' (z _ _ _ (θ.app T') (m'.G.map ψ) - z _ _ _ (m.G.map ψ) (θ.app T'')) =
      -m.a0 T'' (z _ _ _ (m.G.map φ) (m.G.map ψ)) + m'.a0 T'' (z _ _ _ (m'.G.map φ) (m'.G.map ψ))
    have e1 := congrArg (m'.a0 T'') (h1 _ _ _ _ (m.G.map φ) (m.G.map ψ) (θ.app T''))
    have e2 := congrArg (m'.a0 T'') (h1 _ _ _ _ (m.G.map φ) (θ.app T') (m'.G.map ψ))
    have e3 := congrArg (m'.a0 T'') (h1 _ _ _ _ (θ.app T) (m'.G.map φ) (m'.G.map ψ))
    rw [θ.naturality ψ] at e1
    rw [θ.naturality φ] at e2
    rw [← m.G.map_comp] at e1
    rw [← m'.G.map_comp] at e3
    simp only [map_add (f := _), j.e0, m'.compDegreeZero_natural] at e1 e2 e3
    simp only [map_sub, m'.compDegreeZero_natural]
    linear_combination (norm := abel1) e1 - e2 + e3
  · change m'.a1 T' (w _ _ (θ.app T')) - K'.M1.map φ (m'.a1 T (w _ _ (θ.app T))) -
        K'.d0 T' (m'.a0 T' (z _ _ _ (θ.app T) (m'.G.map φ) - z _ _ _ (m.G.map φ) (θ.app T'))) =
      -m.a1 T' (w _ _ (m.G.map φ)) + m'.a1 T' (w _ _ (m'.G.map φ))
    have e := congrArg (m'.a1 T') ((h2 _ _ _ (m.G.map φ) (θ.app T')).symm.trans
      ((congrArg (w _ _) (θ.naturality φ)).trans (h2 _ _ _ (θ.app T) (m'.G.map φ))))
    simp only [map_add (f := _), j.e1, m'.compDegreeOne_natural, m'.comp_commutes_diffZero] at e
    simp only [map_sub]
    linear_combination (norm := abel1) e
  · change K'.d1 T (m'.a1 T (w _ _ (θ.app T))) = -m.a2 T (η _) + m'.a2 T (η _)
    rw [h3 _ _ (θ.app T), map_add (f := _), j.e2, m'.comp_commutes_diffOne]; abel

theorem joinedTwo_inst : JoinedTwo.{1,1} ∧ JoinedTwo.{1,0} ∧ JoinedTwo.{0,0} := ⟨main, main, main⟩

end GlobalTheory.CxCoh.JoinedTwoProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelwiseEquivalenceIsEquivalenceStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelwiseEquivalence_isEquivalence : GlobalTheory.EtC.A3 := by
  first | (exact @GlobalTheory.EtC.levelwise_eqv) | (exact GlobalTheory.EtC.levelwise_eqv) | (intros; apply GlobalTheory.EtC.levelwise_eqv  <;> assumption)
end

