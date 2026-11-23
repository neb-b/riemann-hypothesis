module

public import Development.EtaleCohomology.CohomologicalPurity.OffContStepPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc
public import Development.EtaleCohomology.KummerTheory.Bundle0012
public import Development.EtaleCohomology.EtaleSheaves.LeafTwPairExistsPfExt
public import Development.EtaleCohomology.EtaleSheaves.Bundle0015
public import Development.EtaleCohomology.EtaleSheaves.LeafTwTensResPf
public import Development.EtaleCohomology.TateTwists.Bundle0026
public import Development.EtaleCohomology.TateTwists.Bundle0016
public import Development.EtaleCohomology.TateTwists.Bundle0015
public import Development.EtaleCohomology.TateTwists.Bundle0023
public import Development.EtaleCohomology.TateTwists.conePf
public import Development.EtaleCohomology.TateTwists.Bundle0030
public import Development.EtaleCohomology.TateTwists.Bundle0033
public import Development.EtaleCohomology.TateTwists.Bundle0031
public import Development.EtaleCohomology.TateTwists.Bundle0018
public import Development.EtaleCohomology.TateTwists.Bundle0010
public import Development.EtaleCohomology.TateTwists.Bundle0027
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0020
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0013
public import Development.EtaleCohomology.CohomologicalPurity.LeafChPushPf

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.EtalePurityContinuityOffClosedOfLocalAndChase
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem pairFiveS_surj (bd : LeafBd) (q : ℕ) {J : Type} [SmallCategory J] [IsFiltered J] (F : Jᵒᵖ ⥤ Arrow Spc)
    (P : Arrow Spc) (c : ∀ j, P ⟶ F.obj (op j)) (hc : ∀ j k (f : j ⟶ k), c k ≫ F.map f.op = c j)
    (hm : ∀ j, Mono (F.obj (op j)).hom) (hP : Mono P.hom) (i : ℤ) (hL : ∀ m, ContL q F P c m i)
    (hR : ∀ m, ContR q F P c m i) (m : ℤ) (x : Hs q P (m + 1) i) :
    ∃ j, ∃ y, Hs.pull q (c j) (m + 1) i y = x := by
  obtain ⟨δ, hex, hnat, -⟩ := bd
  obtain ⟨j, y, hy⟩ := (hR (m + 1)).1 (Hs.fgt q P (m + 1) i x)
  have h0 : pull _ (c j).left (tw q i) (m + 1) (pull _ (F.obj (op j)).hom (tw q i) (m + 1) y) = 0 := by
    rw [← GlobalTheory.EtC.pull_comp, Arrow.w (c j), GlobalTheory.EtC.pull_comp, hy]
    exact ((hex q P hP (m + 1) i).1 _).mpr ⟨x, rfl⟩
  obtain ⟨k, f, hk⟩ := (hL (m + 1)).2 j _ h0
  have hk' : pull _ (F.obj (op k)).hom (tw q i) (m + 1) (pull _ (F.map f.op).right (tw q i) (m + 1) y) = 0 := by
    rw [← GlobalTheory.EtC.pull_comp, ← Arrow.w (F.map f.op), GlobalTheory.EtC.pull_comp, hk]
  obtain ⟨s, hs⟩ := ((hex q _ (hm k) (m + 1) i).1 _).mp hk'
  have hv : Hs.fgt q P (m + 1) i (x - Hs.pull q (c k) _ _ s) = 0 := by
    rw [map_sub, Hs.fgt_pull, hs, ← GlobalTheory.EtC.pull_comp, ← Arrow.comp_right, hc, hy, sub_self]
  obtain ⟨u, hu⟩ := ((hex q P hP m i).2.2 _).mp hv
  obtain ⟨l, a, ha⟩ := (hL m).1 u
  rw [← ha, ← hnat q _ _ (c l) hP (hm l)] at hu
  obtain ⟨M, g1, g2, -⟩ := IsFilteredOrEmpty.cocone_objs k l
  refine ⟨M, Hs.pull q (F.map g1.op) _ _ s + Hs.pull q (F.map g2.op) _ _ (δ q _ m i a), ?_⟩
  rw [map_add (f := _), ← Hs.pullComp, ← Hs.pullComp, hc, hc, hu, add_sub_cancel]

theorem pairFiveS_inj (bd : LeafBd) (q : ℕ) {J : Type} [SmallCategory J] [IsFiltered J] (F : Jᵒᵖ ⥤ Arrow Spc)
    (P : Arrow Spc) (c : ∀ j, P ⟶ F.obj (op j)) (hc : ∀ j k (f : j ⟶ k), c k ≫ F.map f.op = c j)
    (hm : ∀ j, Mono (F.obj (op j)).hom) (hP : Mono P.hom) (i : ℤ) (hL : ∀ m, ContL q F P c m i)
    (hR : ∀ m, ContR q F P c m i) (m : ℤ) (j : J) (y : Hs q (F.obj (op j)) (m + 1) i)
    (hy : Hs.pull q (c j) (m + 1) i y = 0) :
    ∃ (k : J) (f : j ⟶ k), Hs.pull q (F.map f.op) (m + 1) i y = 0 := by
  obtain ⟨δ, hex, hnat, -⟩ := bd
  have h0 : pull _ (c j).right (tw q i) (m + 1) (Hs.fgt q _ (m + 1) i y) = 0 := by
    rw [← Hs.fgt_pull, hy, map_zero]
  obtain ⟨k, f, hk⟩ := (hR (m + 1)).2 j _ h0
  rw [← Hs.fgt_pull] at hk
  obtain ⟨a, ha⟩ := ((hex q _ (hm k) m i).2.2 _).mp hk
  have hz : δ q P m i (pull _ (c k).left (tw q i) m a) = 0 := by
    rw [← hnat q _ _ (c k) hP (hm k), ha, ← Hs.pullComp, hc, hy]
  obtain ⟨b, hb⟩ := ((hex q P hP m i).2.1 _).mp hz
  obtain ⟨l, e, he⟩ := (hR m).1 b
  obtain ⟨M, g1, g2, -⟩ := IsFilteredOrEmpty.cocone_objs k l
  have hd : pull _ (c M).left (tw q i) m (pull _ (F.map g1.op).left (tw q i) m a -
      pull _ (F.obj (op M)).hom (tw q i) m (pull _ (F.map g2.op).right (tw q i) m e)) = 0 := by
    rw [map_sub, ← GlobalTheory.EtC.pull_comp, ← Arrow.comp_left, hc, ← hb, ← he, ← GlobalTheory.EtC.pull_comp,
      ← GlobalTheory.EtC.pull_comp, ← GlobalTheory.EtC.pull_comp, Category.assoc, ← Arrow.w (F.map g2.op), ← Category.assoc, ← Arrow.comp_left, hc,
      Arrow.w (c l), sub_self]
  obtain ⟨p, h, hp⟩ := (hL m).2 M _ hd
  rw [map_sub, sub_eq_zero, ← GlobalTheory.EtC.pull_comp, ← Arrow.comp_left, ← F.map_comp, ← op_comp,
    ← GlobalTheory.EtC.pull_comp, Arrow.w (F.map h.op), GlobalTheory.EtC.pull_comp] at hp
  refine ⟨p, f ≫ g1 ≫ h, ?_⟩
  have e1 : F.map (f ≫ g1 ≫ h).op = F.map (g1 ≫ h).op ≫ F.map f.op := by rw [op_comp, F.map_comp]
  rw [e1, Hs.pullComp, ← ha, hnat q _ _ _ (hm p) (hm k), hp]
  exact ((hex q _ (hm p) m i).2.1 _).mpr ⟨_, rfl⟩

theorem pairFiveS : PairFiveS := by
  intro bd q J _ _ F P c hc hm hP i hL hR n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  exact ⟨pairFiveS_surj bd q F P c hc hm hP i hL hR m,
    fun j y hy => pairFiveS_inj bd q F P c hc hm hP i hL hR m j y hy⟩

theorem etale_purity_continuity_off_closed_of_local_and_chase (hL : OffContLoc) (hG : OffChaseGeo) : OffContStep :=
  etale_complement_continuity_induction_of_localization_and_pair_lemmas hL pairFiveS hG

end LateralTheory.CohomologicalPurity
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafAWCut
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.EtaleFoundations

namespace LateralTheory.CohomologicalPurity.LeafAWCut

def LeafTwSec : Prop := EtaleTateTwistSectionsLocallyGenerated

theorem of_pair (h : LateralTheory.E.CupProductRingLaws.LeafTwPairExists) : LateralTheory.CohomologicalPurity.LeafAW := by
  intro q _ i j
  exact ⟨pick_spec (h q i j), fun E n m α β => LateralTheory.KummerTheory.CupAW_of (ZMod q) (twPair q i j) E rfl α β⟩

theorem row : EtaleTensorWithFlatPreservesLocalExactness := by
  intro R _ C J hJ hC s t V x hx
  have hA : C.Acyclic := fun n => (etale_short_complex_exact_iff_locally_surjective_on_kernel R (C.sc n)).2 (hC n)
  exact acyc.column_of R C J hJ ((acyc.acycIff_of R C).1 hA) V s t x hx

theorem tensAcyc : EtaleTensorAcyclicOfFlatBounded :=
  etale_tensor_complex_acyclic_of_locally_exact_flat etale_short_complex_exact_iff_locally_surjective_on_kernel (etale_tensor_complex_locally_exact_of_lifted_sections
    (etale_tensor_cycles_locally_lift_of_row_exact_and_descent row etale_tensor_cycle_locally_lowers_top_degree_of_row_exact))

theorem tensQis : EtaleTensorPairQuasiIsoOfFlatQuasiIso := etale_tensor_preserves_quasiIso_of_acyclic_and_cone tensAcyc tqis.cone_of

theorem pair_of (hq : EtaleTensorPairQuasiIsoOfFlatQuasiIso) (hm : EtaleTateTwistSingletonTensorGenMul) : LateralTheory.E.CupProductRingLaws.LeafTwPairExists :=
  LateralTheory.E.LeafTwPairExistsPf.LeafTwPairExists_of' LateralTheory.E.LeafTwTensExPf.LeafTwTensEx_of
    (LateralTheory.E.LeafTwTensResPf.leafTwTensRes_of
      (etale_tensor_twisted_resolution_of_existence_bound_and_sides LateralTheory.Fin.EtaleComplexTensorPairingExists.intersectionNumber_baseChange
        (fun R _ _ _ _ μ hI hJ hμ => (LateralTheory.Fin.EtaleTensorPairUniversalProperty.intersectionNumber_baseChange R μ hμ).2.1 hI hJ)
        (tt_twist_side_of hm LateralTheory.Fin.EtaleTateTwistSheafFlat.intersectionNumber_baseChange LateralTheory.Fin.EtaleComplexPairingFlipExists.intersectionNumber_baseChange hq)
        (tt_res_side_of LateralTheory.Fin.EtaleTensorPairUniversalProperty.intersectionNumber_baseChange hq))
      (fun q _ j t => (LateralTheory.Fin.EtaleTwistResolutionUniversalExtension.intersectionNumber_baseChange q j).2.1 t))

theorem twMul (hT : LeafTwSec) : EtaleTateTwistSingletonTensorGenMul :=
  etale_tate_twist_tensor_iso_of_generator_map_iso (etale_tate_twist_multiplication_tensor_exists_of_complex_tensor_exists LateralTheory.Fin.EtaleComplexTensorPairingExists.intersectionNumber_baseChange) (etale_tate_twist_multiplication_generator_map_of_section_description hT)
    (etale_tate_twist_generator_map_isIso_of_inj_surj etale_sheaf_mono_epi_iff_sections_of_separation
      (etale_tate_twist_generator_map_surjective_of_local_and_root (fun q _ i => (hT q i).1)
        (fun q _ j => ⟨(hT q j).2.2.2.1, fun U ζ ξ => (hT q j).2.1 U ζ (twGen j ξ)⟩))
      (etale_tate_twist_generator_map_injective_of_sections_glue hT LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue.intersectionNumber_baseChange))

theorem goal_of (h2 : LeafTwSec) : LateralTheory.CohomologicalPurity.LeafAW :=
  of_pair (pair_of tensQis (twMul h2))

end LateralTheory.CohomologicalPurity.LeafAWCut
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafAugInjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def EtaleOpenCovSieve : Prop := ∀ (T : Scheme.{0}) (S : Sieve T),
  (∀ t : T, ∃ V : T.Opens, t ∈ V ∧ S V.ι) → S ∈ Scheme.etaleTopology.{0} T

def EtaleAugInjAt : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R] (n : ℕ)
    (T : Scheme.{0}ᵒᵖ) (x : ((((chainsP R).obj (hoc (D ⋙ yoneda))).X n).obj T)),
    Cyc _ n T x → Bdy _ n T ((((chainsP R).map (aug _ hc)).f n).app T |>.hom x) →
    ∀ t : T.unop, ∃ V : T.unop.Opens, t ∈ V ∧
      Bdy _ n (op (V : Scheme.{0})) (((((chainsP R).obj (hoc (D ⋙ yoneda))).X n).map V.ι.op).hom x)

theorem bdy_res {R : Type} [CommRing R] (K : PCx R) (n : ℕ) {U V : Scheme.{0}} (g : V ⟶ U) (x : (K.X n).obj (op U))
    (h : Bdy K n (op U) x) : Bdy K n (op V) (((K.X n).map g.op).hom x) := by
  obtain ⟨y, rfl⟩ := h
  refine ⟨((K.X (n + 1)).map g.op).hom y, ?_⟩
  have := (K.d (n + 1) n).naturality g.op
  exact (ConcreteCategory.congr_hom this y).symm.trans rfl |>.symm ▸ rfl

def bdySieve {R : Type} [CommRing R] (K : PCx R) (n : ℕ) (T : Scheme.{0}) (x : (K.X n).obj (op T)) : Sieve T where
  arrows U f := Bdy K n (op U) (((K.X n).map f.op).hom x)
  downward_closed {U V} f hf g := by
    have e : ((K.X n).map (g ≫ f).op).hom x = ((K.X n).map g.op).hom (((K.X n).map f.op).hom x) := by
      rw [op_comp, Functor.map_comp]; rfl
    rw [e]; exact bdy_res K n g _ hf

theorem EtaleAugInj_of_openCovSieve (hc0 : EtaleOpenCovSieve) (ha : EtaleAugInjAt) : LeafAugInj := by
  intro J _ D X c ho hcov hdir hc R _ n T x hx hb
  refine ⟨bdySieve _ n T.unop x, hc0 _ _ fun t => ?_, fun U f hf => hf⟩
  obtain ⟨V, hV, h⟩ := ha J D X c ho hcov hdir hc R n T x hx hb t
  exact ⟨V, hV, h⟩

theorem etaleOpenCovSieve : EtaleOpenCovSieve := by
  intro T S h
  choose V hV hS using h
  apply Scheme.zariskiTopology_le_etaleTopology
  rw [Scheme.zariskiTopology, Scheme.mem_grothendieckTopology_iff]
  refine ⟨Scheme.Cover.mkOfCovers T (fun t => (V t : Scheme.{0})) (fun t => (V t).ι)
    (fun x => ⟨x, ⟨x, hV x⟩, by simp⟩), ?_⟩
  rintro Y g ⟨i⟩
  exact hS i

theorem EtaleAugInj_of_augInjAt (ha : EtaleAugInjAt) : LeafAugInj := EtaleAugInj_of_openCovSieve etaleOpenCovSieve ha

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafAugSurjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem altSum (m : ℕ) : ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) = if Even m then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i) (m + 2)]
  induction m with
  | zero => simp [Finset.sum_range_succ]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd m with h | h
    · have h' : ¬ Even (m + 1) := by simpa [Nat.even_add_one] using h
      simp [h, h', pow_succ, h.neg_one_pow]
    · have h' : Even (m + 1) := by simpa [Nat.even_add_one, Nat.not_even_iff_odd] using h
      have hn : ¬ Even m := Nat.not_even_iff_odd.2 h
      simp [hn, h', pow_succ, h.neg_one_pow]

theorem dL {R : Type} [CommRing R] (Y : PSh) (m : ℕ) (T : Scheme.{0}ᵒᵖ) (z : ((((chainsP R).obj (disc.obj Y)).X (m + 1)).obj T)) :
    ((((chainsP R).obj (disc.obj Y)).d (m + 1) m).app T).hom z = (∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ)) • z := by
  change (((freeP R).obj Y).obj T) at z
  have e : ∀ i : Fin (m + 2), SimplicialObject.δ (disc.obj Y) i = 𝟙 _ := fun _ => rfl
  simp [chainsP, e]
  erw [LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using
    (Module.End.intCast_apply (R := ULift.{1} R) ((-1 : ℤ) ^ (i : ℕ)) z)

section
variable {R : Type} [CommRing R]

theorem bdyL (Y : PSh) (n : ℕ) (T : Scheme.{0}ᵒᵖ) (x : ((((chainsP R).obj (disc.obj Y)).X (n + 1)).obj T))
    (hx : Cyc ((chainsP R).obj (disc.obj Y)) (n + 1) T x) : Bdy ((chainsP R).obj (disc.obj Y)) (n + 1) T x := by
  by_cases h : Even (n + 1)
  · have h0 := hx n
    rw [dL, altSum, if_neg (by simpa [Nat.even_add_one] using h)] at h0
    simp only [one_smul] at h0
    exact ⟨0, by rw [map_zero]; exact h0.symm⟩
  · refine ⟨x, ?_⟩
    have e := dL (R := R) Y (n + 1) T x
    rw [altSum, if_neg h] at e
    exact e.trans (one_smul ℤ _)

def imSv {K L : PCx R} (φ : K ⟶ L) (n : ℕ) {T : Scheme.{0}} (y : (L.X n).obj (op T)) : Sieve T where
  arrows U f := ∃ x', ((φ.f n).app (op U)).hom x' = ((L.X n).map f.op).hom y
  downward_closed := by
    rintro U V f ⟨x', hx⟩ g
    refine ⟨((K.X n).map g.op).hom x', ?_⟩
    have h1 := congrArg (fun h => h.hom x') ((φ.f n).naturality g.op)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    rw [h1, hx, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem imSv_add {K L : PCx R} (φ : K ⟶ L) (n : ℕ) {T : Scheme.{0}} (y z : (L.X n).obj (op T)) :
    imSv φ n y ⊓ imSv φ n z ≤ imSv φ n (y + z) := by
  rintro U f ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩

theorem imSv_smul {K L : PCx R} (φ : K ⟶ L) (n : ℕ) {T : Scheme.{0}} (y : (L.X n).obj (op T)) (r : ULift.{1} R) :
    imSv φ n y ≤ imSv φ n (r • y) := by
  rintro U f ⟨a, ha⟩
  exact ⟨r • a, by rw [map_smul, map_smul, ha]⟩

theorem imSv_zero {K L : PCx R} (φ : K ⟶ L) (n : ℕ) {T : Scheme.{0}} :
    imSv φ n (0 : (L.X n).obj (op T)) = ⊤ := by
  ext U f
  simp only [Sieve.top_apply, iff_true]
  exact ⟨0, by rw [map_zero, map_zero]⟩

end

section
variable {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X)
  (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R]

theorem gen_mem (hcov : ∀ x : X, ∃ j, x ∈ Set.range (c j)) [∀ j, IsOpenImmersion (c j)]
    {T : Scheme.{0}} (g : T ⟶ X) :
    imSv ((chainsP R).map (aug _ hc)) 0
      (ModuleCat.freeMk (ULift.up g) : (((chainsP R).obj (disc.obj (yoneda.obj X))).X 0).obj (op T)) ∈
      Scheme.etaleTopology T := by
  let j : T → J := fun t => (hcov (g t)).choose
  let V : T → T.Opens := fun t => g ⁻¹ᵁ (c (j t)).opensRange
  have hV : ∀ t, t ∈ V t := fun t => (hcov (g t)).choose_spec
  let 𝒰 : T.Cover (Scheme.precoverage @Etale) := Scheme.Cover.mkOfCovers T (fun t => (V t).toScheme)
    (fun t => (V t).ι) (fun t => ⟨t, ⟨t, hV t⟩, by simp⟩)
  refine GrothendieckTopology.superset_covering _ ?_ 𝒰.mem_grothendieckTopology
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨t⟩
  have hr : Set.range ((V t).ι ≫ g) ⊆ Set.range (c (j t)) := by
    rintro _ ⟨y, rfl⟩
    have := (V t).range_ι ▸ Set.mem_range_self (f := (V t).ι) y
    simpa [V] using this
  let a := IsOpenImmersion.lift (c (j t)) ((V t).ι ≫ g) hr
  let σ : Fin (0 + 1) ⥤ J := (Functor.const _).obj (j t)
  refine ⟨ModuleCat.freeMk (ULift.up ((inj (D ⋙ yoneda) (op (SimplexCategory.mk 0)) σ).app (op (V t).toScheme) a)), ?_⟩
  erw [ModuleCat.free_map_apply, ModuleCat.free_map_apply]
  refine congrArg ModuleCat.freeMk (ULift.ext ?_)
  show (a ≫ D.map (𝟙 (j t))) ≫ c (j t) = (V t).ι ≫ g
  rw [D.map_id, Category.comp_id]
  exact IsOpenImmersion.lift_fac _ _ _
end

theorem all_mem {J : Type} [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X)
    (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R]
    (hcov : ∀ x : X, ∃ j, x ∈ Set.range (c j)) [∀ j, IsOpenImmersion (c j)] {T : Scheme.{0}}
    (x : (((chainsP R).obj (disc.obj (yoneda.obj X))).X 0).obj (op T)) :
    imSv ((chainsP R).map (aug _ hc)) 0 x ∈ Scheme.etaleTopology T := by
  let M := (((chainsP R).obj (disc.obj (yoneda.obj X))).X 0).obj (op T)
  let b : Module.Basis (ULift.{1} (T ⟶ X)) (ULift.{1} R) M := Finsupp.basisSingleOne
  have hx : x ∈ Submodule.span (ULift.{1} R) (Set.range b) := b.mem_span x
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨g⟩, rfl⟩ := hy
    exact gen_mem D X c hc R hcov g
  | zero => rw [imSv_zero]; exact GrothendieckTopology.top_mem _ _
  | add y z _ _ hy hz =>
    exact GrothendieckTopology.superset_covering _ (imSv_add _ _ y z)
      (GrothendieckTopology.intersection_covering _ hy hz)
  | smul r y _ hy => exact GrothendieckTopology.superset_covering _ (imSv_smul _ _ y r) hy

theorem LeafAugSurj_of : LeafAugSurj := by
  intro J _ D X c ho hcov hc R _ n T x hx
  rcases n with _ | n
  · refine ⟨imSv ((chainsP R).map (aug _ hc)) 0 x, ?_, ?_⟩
    · have := ho
      exact all_mem D X c hc R hcov x
    · rintro U f ⟨x', hx'⟩
      refine ⟨x', fun m => ?_, 0, ?_⟩
      · rw [HomologicalComplex.shape _ 0 m (by simp)]
        rfl
      · rw [map_zero, hx', sub_self]
  · refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun U f _ => ⟨0, fun m => by simp, ?_⟩⟩
    obtain ⟨y, hy⟩ := bdyL _ n T x hx
    refine ⟨-((((chainsP R).obj (disc.obj (yoneda.obj X))).X (n + 1 + 1)).map f.op).hom y, ?_⟩
    have h := congrArg (fun h => h.hom y) ((((chainsP R).obj (disc.obj (yoneda.obj X))).d (n + 1 + 1) (n + 1)).naturality f.op)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [map_neg, map_zero, zero_sub, h, hy]

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafExcOfEqvPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

@[reassoc] theorem dinl_map {A B : Arrow Spc} (ψ : A ⟶ B) : dbl.inl A ≫ dbl.map ψ = ψ.right ≫ dbl.inl B :=
  pushout.inl_desc (f := A.hom) (g := A.hom) _ _ _

variable {P' P : Arrow Spc} (φ : P' ⟶ P)

def ii : P'.right ⟶ MM φ := pushout.inl P'.hom (P'.hom ≫ φ.right)
def jj : P.right ⟶ MM φ := pushout.inr P'.hom (P'.hom ≫ φ.right)
theorem ij_cond : P'.hom ≫ ii φ = (P'.hom ≫ φ.right) ≫ jj φ :=
  pushout.condition (f := P'.hom) (g := P'.hom ≫ φ.right)

def rr : MM φ ⟶ P.right :=
  pushout.desc (f := P'.hom) (g := P'.hom ≫ φ.right) φ.right (𝟙 _) (by simp)

def QQ : Arrow Spc := Arrow.mk (jj φ)

def chi : P' ⟶ QQ φ := Arrow.homMk (P'.hom ≫ φ.right) (ii φ) (ij_cond φ).symm

def sig : dbl (QQ φ) ⟶ MM φ :=
  pushout.desc (f := jj φ) (g := jj φ) (𝟙 _) (rr φ ≫ jj φ) (by
    have h : jj φ ≫ rr φ = 𝟙 _ :=
      pushout.inr_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
    rw [← Category.assoc, h, Category.id_comp, Category.comp_id])

theorem inr_sig_gM : dbl.inr (QQ φ) ≫ sig φ ≫ gM φ = rr φ ≫ dbl.inr P := by
  have hs : dbl.inr (QQ φ) ≫ sig φ = rr φ ≫ jj φ :=
    pushout.inr_desc (f := jj φ) (g := jj φ) _ _ _
  have hg : jj φ ≫ gM φ = dbl.inr P :=
    pushout.inr_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
  rw [← Category.assoc, hs]
  change (rr φ ≫ jj φ) ≫ gM φ = rr φ ≫ dbl.inr P
  rw [Category.assoc, hg]

theorem hgM : dbl.map (chi φ) ≫ sig φ ≫ gM φ = dbl.map φ := by
  have hs : dbl.inl (QQ φ) ≫ sig φ = 𝟙 _ :=
    pushout.inl_desc (f := jj φ) (g := jj φ) _ _ _
  have hg : ii φ ≫ gM φ = φ.right ≫ dbl.inl P :=
    pushout.inl_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
  have hr : ii φ ≫ rr φ = φ.right :=
    pushout.inl_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
  apply pushout.hom_ext
  · show dbl.inl P' ≫ _ = dbl.inl P' ≫ _
    rw [dinl_map_assoc, dinl_map, ← Category.assoc (dbl.inl (QQ φ)), hs]
    change ii φ ≫ 𝟙 (MM φ) ≫ gM φ = _
    rw [Category.id_comp]
    exact hg
  · show dbl.inr P' ≫ _ = dbl.inr P' ≫ _
    rw [← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, inr_sig_gM]
    change ii φ ≫ rr φ ≫ dbl.inr P = _
    rw [← Category.assoc, hr]

end LateralTheory.CohomologicalPurity.TubeCut

namespace LateralTheory.CohomologicalPurity.TubeCut
variable {P' P : Arrow Spc} (φ : P' ⟶ P)
theorem jj_inl : jj φ ≫ dbl.inl (QQ φ) = jj φ ≫ dbl.inr (QQ φ) :=
  pushout.condition (f := jj φ) (g := jj φ)

def LeafFix : Prop := ∀ (q : ℕ) (n i : ℤ) {P' P : Arrow Spc} (φ : P' ⟶ P) (z : Ht q (dbl (QQ φ)) n i),
  z ∈ Hs q (QQ φ) n i → pull _ (sig φ ≫ dbl.inl (QQ φ)) (tw q i) n z = z

def LeafChiExc : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), Exc q (chi φ)

theorem pull_sig_inl (q : ℕ) (n i : ℤ) (z : Ht q (dbl (QQ φ)) n i) :
    pull _ (sig φ) (tw q i) n (pull _ (dbl.inl (QQ φ)) (tw q i) n z) = pull _ (sig φ ≫ dbl.inl (QQ φ)) (tw q i) n z :=
  (pull_comp _ (sig φ) (dbl.inl (QQ φ)) _ n z).symm

theorem pull_jj_inl (q : ℕ) (n i : ℤ) (z : Ht q (dbl (QQ φ)) n i) (hz : z ∈ Hs q (QQ φ) n i) :
    pull _ (jj φ) (tw q i) n (pull _ (dbl.inl (QQ φ)) (tw q i) n z) = 0 := by
  have hzz : pull _ (dbl.inr (QQ φ)) (tw q i) n z = 0 := hz
  exact (pull_comp _ (jj φ) (dbl.inl (QQ φ)) _ n z).symm.trans
    ((congrArg (fun f => pull _ f (tw q i) n z) (jj_inl φ)).trans
      ((pull_comp _ (jj φ) (dbl.inr (QQ φ)) _ n z).trans ((congrArg (pull _ (jj φ) (tw q i) n) hzz).trans (map_zero _))))

theorem LeafExcOfEqv_of (hF : LeafFix) (hX : LeafChiExc) : LeafExcOfEqv := by
  intro q P' P φ hE n i
  have jj_gM : jj φ ≫ gM φ = dbl.inr P :=
    pushout.inr_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
  have inr_sig : dbl.inr (QQ φ) ≫ sig φ = rr φ ≫ jj φ :=
    pushout.inr_desc (f := jj φ) (g := jj φ) _ _ _
  have inl_sig : dbl.inl (QQ φ) ≫ sig φ = 𝟙 _ :=
    pushout.inl_desc (f := jj φ) (g := jj φ) _ _ _
  have hB : Function.Bijective (pull _ (gM φ) (tw q i) n) := hE i n
  have hC := hX q φ n i
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    have hw' : pull _ (dbl.map φ) (tw q i) n w.1 = 0 := congrArg Subtype.val hw
    have hj : pull _ (jj φ) (tw q i) n (pull _ (gM φ) (tw q i) n w.1) = 0 := by
      rw [← pull_comp, jj_gM]; exact w.2
    have hz : pull _ (sig φ) (tw q i) n (pull _ (gM φ) (tw q i) n w.1) ∈ Hs q (QQ φ) n i := by
      change pull _ (dbl.inr (QQ φ)) _ n (pull _ (sig φ) _ n _) = 0
      exact (pull_comp _ (dbl.inr (QQ φ)) (sig φ) _ n _).symm.trans
        ((congrArg (fun f => pull _ f (tw q i) n (pull _ (gM φ) (tw q i) n w.1)) inr_sig).trans
          ((pull_comp _ (rr φ) (jj φ) _ n _).trans ((congrArg (pull _ (rr φ) (tw q i) n) hj).trans (map_zero _))))
    have h0 : Hs.pull q (chi φ) n i ⟨_, hz⟩ = Hs.pull q (chi φ) n i 0 := by
      rw [map_zero]
      apply Subtype.ext
      change pull _ (dbl.map (chi φ)) _ n (pull _ (sig φ) _ n (pull _ (gM φ) _ n w.1)) = 0
      rw [← pull_comp, ← pull_comp, Category.assoc, hgM]; exact hw'
    have h1 := congrArg Subtype.val (hC.1 h0)
    change pull _ (sig φ) _ n (pull _ (gM φ) _ n w.1) = 0 at h1
    have h2 : pull _ (gM φ) (tw q i) n w.1 = 0 := by
      have e := congrArg (pull _ (dbl.inl (QQ φ)) (tw q i) n) h1
      have e2 : pull _ (dbl.inl (QQ φ)) (tw q i) n (pull _ (sig φ) (tw q i) n (pull _ (gM φ) (tw q i) n w.1)) =
          pull _ (gM φ) (tw q i) n w.1 :=
        (pull_comp _ (dbl.inl (QQ φ)) (sig φ) _ n _).symm.trans
          ((congrArg (fun f => pull _ f (tw q i) n (pull _ (gM φ) (tw q i) n w.1)) inl_sig).trans (pull_id _ _ _ n _))
      rw [e2, map_zero] at e
      exact e
    apply Subtype.ext
    exact hB.1 (h2.trans (map_zero _).symm)
  · intro z'
    obtain ⟨z, hz⟩ := hC.2 z'
    obtain ⟨y', hy'⟩ := hB.2 (pull _ (dbl.inl (QQ φ)) (tw q i) n z.1)
    have hm : y' ∈ Hs q P n i := by
      change pull _ (dbl.inr P) _ n y' = 0
      rw [← jj_gM, pull_comp, hy']
      exact pull_jj_inl φ q n i z.1 z.2
    refine ⟨⟨y', hm⟩, ?_⟩
    rw [← hz]
    apply Subtype.ext
    change pull _ (dbl.map φ) _ n y' = pull _ (dbl.map (chi φ)) _ n z.1
    rw [← hgM, pull_comp, pull_comp, hy', pull_sig_inl, hF q n i φ z.1 z.2]

end LateralTheory.CohomologicalPurity.TubeCut
end
end

