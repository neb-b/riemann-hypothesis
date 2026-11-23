module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0331
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0308
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyClassDiesOnLocalizationAway

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicPreservesSchwartzBruhat
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem parFun_mem : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ φ ∈ SB (Matrix α ν E), parFun c ψ χ Q (mat c p) φ ∈ SB (Matrix α ν E) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ _ _ χ _ _ p hp φ hφ
  obtain ⟨-, hring, -, -, hc, -, htr, -⟩ := _root_.GlobalTheory.quadExt_topology F E c δ hE
  obtain ⟨β, hβ, -, -, -, hform⟩ := _root_.GlobalTheory.KSp.pr_alg F E c δ hE α ν Q hQ
  obtain ⟨hinv, -, -⟩ := _root_.GlobalTheory.KSp.sieg_blocks F E c δ hE ν p hp
  haveI := GlobalTheory.WeilM.nonarch_field F
  set a := (mat c p).toBlocks₁₁ with ha
  set b := (mat c p).toBlocks₁₂ with hb
  set d := (((mat c p).toBlocks₂₂).map c)ᵀ with hd
  have hinv' : d * a = 1 := mul_eq_one_comm.mp hinv
  have hca : Continuous fun x : Matrix α ν E => x * a := continuous_id.matrix_mul continuous_const
  have hcb : Continuous fun x : Matrix α ν E => x * b := continuous_id.matrix_mul continuous_const
  have hcd : Continuous fun x : Matrix α ν E => x * d := continuous_id.matrix_mul continuous_const
  let e : Matrix α ν E ≃ₜ Matrix α ν E :=
    { toFun := fun x => x * a
      invFun := fun x => x * d
      left_inv := fun x => by simp only [Matrix.mul_assoc, hinv, Matrix.mul_one]
      right_inv := fun x => by simp only [Matrix.mul_assoc, hinv', Matrix.mul_one]
      continuous_toFun := hca
      continuous_invFun := hcd }
  have hpr : Continuous fun x : Matrix α ν E => (2⁻¹ : F) * pr c Q (x * a) (x * b) := by
    refine continuous_const.mul ?_
    have : (fun x : Matrix α ν E => pr c Q (x * a) (x * b)) = fun x =>
        2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * ((x * a) * ((x * b).map c)ᵀ))) := by
      funext x; rw [← hβ, hform]
    rw [this]
    exact continuous_const.mul (htr.comp (continuous_const.matrix_mul
      (hca.matrix_mul (hcb.matrix_map hc).matrix_transpose)).matrix_trace)
  have h1 := (GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ).comp_continuous hpr
  have h2 : IsLocallyConstant (φ ∘ fun x : Matrix α ν E => x * a) := hφ.1.comp_continuous hca
  have h3 : HasCompactSupport (φ ∘ e) := hφ.2.comp_homeomorph e
  refine ⟨(IsLocallyConstant.const _).mul (h1.mul h2), ?_⟩
  exact HasCompactSupport.mul_left (HasCompactSupport.mul_left h3)

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicWeylElementGenerateUnitary
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem mem_of_inCell {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
    {ν : Type} [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E)))
    (hP : sieg c ν ≤ U) (hw : weyl c ν ∈ U) {g : UG c (stdJ ν E)} (hg : InCell c g) : g ∈ U := by
  obtain ⟨p, hp, q, hq, rfl⟩ := hg
  exact U.mul_mem (U.mul_mem (hP hp) hw) (hP hq)

theorem sieg_weyl_generate : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E)
    (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E))),
    sieg c ν ≤ U → weyl c ν ∈ U → U = ⊤ := by
  intro F _ _ E _ _ c δ hE ν _ _ U hP hw
  classical
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.KSp.exists_translate_inCell F E c δ hE ν {1, g}
  have h1 : u ∈ U := by
    simpa using mem_of_inCell c U hP hw (hu 1 (by simp))
  have h2 : g * u ∈ U := mem_of_inCell c U hP hw (hu g (by simp))
  simpa using U.mul_mem h2 (U.inv_mem h1)

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicPropertiesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simplicialCochain_classes_basic_properties :
    ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ),
    (∀ s : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F,
      cobd s = 0 → ∃ x : H R E F n, IsCls s x) ∧
    (∀ (s s' : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) (x x' : H R E F n),
      IsCls s x → IsCls s' x' → IsCls (s + s') (x + x')) ∧
    (∀ (s : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) (x x' : H R E F n),
      IsCls s x → IsCls s x' → x = x') ∧
    (∀ (t : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) (x : H R E F ((n + 1 : ℕ) : ℤ)),
      IsCls (cobd t) x → x = 0) ∧
    ∀ (E' : Spc) (f : E' ⟶ E) (s : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) (x : H R E F n),
      IsCls s x → IsCls ((free R).map (f.app (op (SimplexCategory.mk n))) ≫ s) (pull R f F n x) := by
  intro R _ F E n
  have differential (s : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) :
      δ (n : ℤ) ((n + 1 : ℕ) : ℤ)
          (Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n) =
        (((n + 1 : ℕ) : ℤ)).negOnePow • Cochain.single (p := -((n + 1 : ℕ) : ℤ)) (q := 0)
          ((chainsXIso R E (n + 1)).hom ≫ cobd s ≫ resι R F) ((n + 1 : ℕ) : ℤ) := by
    rw [Cochain.δ_single _ (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; ring)
      (-((n + 1 : ℕ) : ℤ)) 1 (by push_cast; ring) rfl]
    rw [Category.assoc, Category.assoc, ClsBasic.resι_d, comp_zero, comp_zero, Cochain.single_zero, zero_add]
    congr 2
    rw [ClsBasic.chains_d, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
    congr 1
    rw [← Category.assoc]
    congr 1
    rw [cobd, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Preadditive.zsmul_comp]
  refine ⟨fun s hs => ?_, fun s s' x x' hx hx' => ?_, fun s x x' hx hx' => ?_,
    fun t x hx => ?_, fun E' f s x hx => ?_⟩
  · refine ⟨CohomologyClass.mk (Cocycle.mk
      (Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n)
      ((n + 1 : ℕ) : ℤ) (by push_cast; ring) ?_), _, rfl, rfl⟩
    rw [differential, hs, zero_comp, comp_zero, Cochain.single_zero, smul_zero]
  · obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hx'
    refine ⟨z + z', (CohomologyClass.mk_add z z').symm, ?_⟩
    change z.1 + z'.1 = _
    rw [hz, hz', ← ClsBasic.single_add', Preadditive.add_comp, Preadditive.comp_add]
  · obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hx'
    have : z = z' := Cocycle.ext (hz.trans hz'.symm)
    rw [this]
  · obtain ⟨z, rfl, hz⟩ := hx
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n : ℤ) (by push_cast; ring)]
    refine ⟨(((n + 1 : ℕ) : ℤ)).negOnePow •
      Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ t ≫ resι R F) n, ?_⟩
    rw [δ_units_smul, differential, smul_smul, Int.units_mul_self, one_smul, hz]
  · obtain ⟨z, rfl, hz⟩ := hx
    refine ⟨zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add _), rfl, ?_⟩
    change (Cochain.ofHom ((chains R).map f)).comp z.1 (zero_add _) = _
    rw [hz, ClsBasic.ofHom_comp_single, ← Category.assoc, ClsBasic.chainsXIso_nat]
    simp only [Category.assoc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainCoboundaryOfClassZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

namespace GlobalTheory.CechOne

theorem cobd_of_isCls_zero :
    ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (s : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F),
      IsCls (R := R) s (0 : H R E F ((1 : ℕ) : ℤ)) →
        ∃ t : (free R).obj (E.obj (op ⦋0⦌)) ⟶ F, s = cobd (R := R) (E := E) (n := 0) t := by
  intro R _ F E s hs
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, hpos⟩ := _root_.GlobalTheory.EtC.res_basic R F
  obtain ⟨z, hz0, hz⟩ := hs
  rw [CohomologyClass.mk_eq_zero_iff] at hz0
  obtain ⟨m, hm, β, hβ⟩ := hz0
  obtain rfl : m = 0 := by push_cast at hm; omega
  have hzv : ∀ (p q : ℤ) (hpq : p + ((1 : ℕ) : ℤ) = q),
      (↑z : Cochain ((chains R).obj E) (res R F) ((1 : ℕ) : ℤ)).v p q hpq =
        (Cochain.single (p := -((1 : ℕ) : ℤ)) (q := 0)
          ((chainsXIso R E 1).hom ≫ s ≫ resι R F) ((1 : ℕ) : ℤ)).v p q hpq := by
    intro p q hpq
    rw [show (↑z : Cochain ((chains R).obj E) (res R F) ((1 : ℕ) : ℤ)) = z.1 from rfl, hz]
  let b := β.v 0 0 (by omega)
  have hb : b ≫ (res R F).d 0 1 = 0 := by
    have e := Cochain.congr_v hβ 0 1 (by norm_num)
    rw [δ_v 0 _ (by norm_num) β 0 1 _ 0 1 (by omega) rfl,
      (hpos E 1 (by norm_num)).eq_of_tgt (((chains R).obj E).d 0 1) 0, zero_comp, smul_zero, add_zero, hzv,
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega)] at e
    exact e
  haveI : Mono (ShortComplex.mk _ _ w).f := hmono
  let t' : ((chains R).obj E).X 0 ⟶ F := hex.lift b hb
  have ht' : t' ≫ resι R F = b := hex.lift_f b hb
  have e := Cochain.congr_v hβ (-((1 : ℕ) : ℤ)) 0 (by omega)
  have h1 : β.v (-((1 : ℕ) : ℤ)) (-1) (by omega) = 0 := (hneg (-1) (by norm_num)).eq_of_tgt _ _
  rw [δ_v 0 _ (by norm_num) β _ 0 _ (-1) 0 (by omega) (by norm_num), h1,
    zero_comp, zero_add, hzv, Cochain.single_v] at e
  rw [show β.v 0 0 (by omega) = b from rfl, ← ht'] at e
  let D : (free R).obj (E.obj (op ⦋1⦌)) ⟶ (free R).obj (E.obj (op ⦋0⦌)) :=
    ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ E i)
  have hd : ((chains R).obj E).d (-((1 : ℕ) : ℤ)) 0 = (chainsXIso R E 1).hom ≫ D ≫ (chainsXIso R E 0).inv :=
    GlobalTheory.EtC.ClsBasic.chains_d (R := R) E 0
  rw [hd] at e
  have hs : s = (((1 : ℕ) : ℤ).negOnePow : ℤ) • (D ≫ (chainsXIso R E 0).inv ≫ t') := by
    apply (cancel_epi (chainsXIso R E 1).hom).1
    apply (cancel_mono (resι R F)).1
    rw [Category.assoc, ← e]
    simp only [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
  refine ⟨(((1 : ℕ) : ℤ).negOnePow : ℤ) • ((chainsXIso R E 0).inv ≫ t'), ?_⟩
  rw [hs]
  simp only [D, cobd, Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Finset.smul_sum,
    smul_smul, Category.assoc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

end GlobalTheory.CechOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceSectionHaarDecompositionStatement
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstant_indicator_mul_slice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (K : Subgroup (GL (Fin a) k)), IsOpen (K : Set (GL (Fin a) k)) → K ≤ KO k (Fin a) →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a ↔ ∃ J, minor Y J ≠ 0) →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice (k := k) a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice (k := k) a d → g.val * Z ∈ slice (k := k) a d → g = 1) →
    IsLocallyConstant (Set.indicator {Y : Matrix (Fin a) (Fin d) k | ∃ x ∈ K, ∃ Z ∈ slice (k := k) a d, Y = x.val * Z}
      (1 : Matrix (Fin a) (Fin d) k → ℂ)) := by
  intro k _ _ _ _ a d K hKo hKO hrank s hs hsec huniq
  set T : Set (Matrix (Fin a) (Fin d) k) := {Y | ∃ x ∈ K, ∃ Z ∈ slice (k := k) a d, Y = x.val * Z} with hTdef
  set O : Set (Matrix (Fin a) (Fin d) k) := {Y | Y.rank = a} with hOdef
  have hmc : ∀ J : Fin a ↪ Fin d, Continuous fun Y : Matrix (Fin a) (Fin d) k => minor Y J := fun J => by
    unfold minor
    exact (continuous_id.matrix_submatrix id J).matrix_det

  have hT : ∀ Y ∈ O, (Y ∈ T ↔ s Y ∈ K) := by
    intro Y hY
    constructor
    · rintro ⟨x, hx, Z, hZ, rfl⟩
      have h1 : ((s (x.val * Z))⁻¹ * x).val * Z ∈ slice (k := k) a d := by
        rw [Units.val_mul, Matrix.mul_assoc]; exact hsec _ hY
      have h2 := huniq Z _ hZ h1
      have h3 : x = s (x.val * Z) := by
        have := congrArg (fun g => s (x.val * Z) * g) h2
        simpa [← mul_assoc] using this
      rw [← h3]; exact hx
    · intro h
      refine ⟨s Y, h, _, hsec Y hY, ?_⟩
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hTmin : ∀ Y ∈ T, ∃ J, valuation k (minor Y J) = 1 := by
    rintro Y ⟨x, hx, Z, ⟨J, hJ, -⟩, rfl⟩
    refine ⟨J, ?_⟩
    rw [minor_mul, minor, hJ, Matrix.det_one, mul_one]
    have := valuation_gdet_of_mem_KO (hKO hx)
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  have hTO : T ⊆ O := by
    intro Y hY
    obtain ⟨J, hJ⟩ := hTmin Y hY
    refine (hrank Y).2 ⟨J, fun h => ?_⟩
    rw [h, map_zero] at hJ
    exact zero_ne_one hJ
  have hOopen : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro Y hY
    obtain ⟨J, hJ⟩ := (hrank Y).1 hY
    have hv : valuation k (minor Y J) ≠ 0 := by simpa using hJ
    have hn := (valuation k).locally_const hv
    have := (hmc J).continuousAt.preimage_mem_nhds hn
    refine Filter.mem_of_superset this fun Y' hY' => (hrank Y').2 ⟨J, fun h0 => ?_⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, h0, map_zero] at hY'
    exact hv hY'.symm
  have hKc : IsClosed (K : Set (GL (Fin a) k)) := Subgroup.isClosed_of_isOpen K hKo
  have hTeq : T = O ∩ s ⁻¹' (K : Set (GL (Fin a) k)) := by
    ext Y
    constructor
    · intro h; exact ⟨hTO h, (hT Y (hTO h)).1 h⟩
    · rintro ⟨h1, h2⟩; exact (hT Y h1).2 h2
  have hTopen : IsOpen T := by
    rw [hTeq]; exact hs.isOpen_inter_preimage hOopen hKo
  have h0 : {x : k | valuation k x < 1} ∈ nhds (0 : k) := by
    have := (IsValuativeTopology.hasBasis_nhds_zero k).mem_of_mem (i := 1) trivial
    simpa using this
  have hTclosed : IsClosed T := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro Y hY
    by_cases hYO : Y ∈ O
    · have hsY : s Y ∉ K := fun h => hY ((hT Y hYO).2 h)
      have ho : IsOpen (O ∩ s ⁻¹' (K : Set (GL (Fin a) k))ᶜ) := hs.isOpen_inter_preimage hOopen hKc.isOpen_compl
      refine Filter.mem_of_superset (ho.mem_nhds ⟨hYO, hsY⟩) fun Y' hY' hT' => hY'.2 ?_
      exact (hT Y' hY'.1).1 hT'
    · have hz : ∀ J, minor Y J = 0 := by
        intro J; by_contra hne; exact hYO ((hrank Y).2 ⟨J, hne⟩)
      have hW : (⋂ J : Fin a ↪ Fin d, (fun Y' => minor Y' J) ⁻¹' {x : k | valuation k x < 1}) ∈ nhds Y := by
        refine Filter.iInter_mem.2 fun J => ?_
        refine (hmc J).continuousAt.preimage_mem_nhds ?_
        rw [hz J]; exact h0
      refine Filter.mem_of_superset hW fun Y' hY' hT' => ?_
      obtain ⟨J, hJ⟩ := hTmin Y' hT'
      have := Set.mem_iInter.1 hY' J
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hJ] at this
      exact lt_irrefl _ this
  exact (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hTclosed, hTopen⟩).isLocallyConstant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceStabilizerTrivialStatement
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slice_stabilizer_trivial : ∀ (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a d : ℕ) (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k),
    Z ∈ slice (k := k) a d → g.val * Z ∈ slice (k := k) a d → g = 1 := by
  rintro k _ _ _ _ a d Z g ⟨J, hJ, hZ⟩ ⟨J', hJ', hgZ⟩
  have hminor : minor Z J = 1 := by rw [minor, hJ, det_one]
  have hminor' : minor (g.val * Z) J' = 1 := by rw [minor, hJ', det_one]
  have hproduct : valuation k (g.val.det) * valuation k (minor Z J') = 1 := by
    rw [← map_mul, ← minor_mul, hminor', map_one]
  have hdet_le : valuation k (g.val.det) ≤ 1 := by
    have h := (hgZ J).1
    rwa [minor_mul, hminor, mul_one] at h
  have hslice : valuation k (minor Z J') = 1 := by
    refine le_antisymm (hZ J').1 ?_
    calc
      (1 : ValueGroupWithZero k) = valuation k (g.val.det) * valuation k (minor Z J') :=
        hproduct.symm
      _ ≤ 1 * valuation k (minor Z J') := mul_le_mul_of_nonneg_right hdet_le zero_le
      _ = valuation k (minor Z J') := one_mul _
  have hdet : valuation k (g.val.det) = 1 := by rwa [hslice, mul_one] at hproduct
  have hindices : J = J' := by
    rcases lt_trichotomy (idx J') (idx J) with h | h | h
    · exact absurd ((hZ J').2 h) (by rw [hslice]; exact lt_irrefl _)
    · exact (idx.injective h).symm
    · have hlt := (hgZ J).2 h
      rw [minor_mul, hminor, mul_one, hdet] at hlt
      exact absurd hlt (lt_irrefl _)
  subst J'
  have hsub : (g.val * Z).submatrix id J = g.val * Z.submatrix id J := by
    ext i j
    simp [Matrix.mul_apply, submatrix_apply]
  rw [hsub, hJ, Matrix.mul_one] at hJ'
  exact Units.ext hJ'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSurjectiveEtaleLocallyHasSections
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem smooth_surjective_loc_sections : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [Smooth f] [Surjective f] (U : Scheme.{0}) (y : U ⟶ X), Loc U fun V g => ∃ x : V ⟶ Y, x ≫ f = g ≫ y := by
  intro Y X f _ _ U y
  refine (loc_iff_etale_affine_points U (fun V g => ∃ x : V ⟶ Y, x ≫ f = g ≫ y) ?_).2 ?_
  · rintro V W g k ⟨x, hx⟩
    exact ⟨k ≫ x, by simp [Category.assoc, hx]⟩
  · intro u
    obtain ⟨V, s, hE, hu⟩ := _root_.GlobalTheory.exists_etale_quasiSection_of_smooth f (y u) (f.surjective (y u))
    obtain ⟨v, hv⟩ := hu
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback v u hv
    let W := pullback (s ≫ f) y
    obtain ⟨z, hz⟩ := W.affineCover.covers w
    haveI := hE
    have hEt : Etale (pullback.snd (s ≫ f) y) := inferInstance
    refine ⟨_, W.affineCover.f (W.affineCover.idx w) ≫ pullback.snd (s ≫ f) y, inferInstance, inferInstance, ⟨z, ?_⟩, ?_⟩
    · simp [hz, hw2]
    · refine ⟨W.affineCover.f (W.affineCover.idx w) ≫ pullback.fst (s ≫ f) y ≫ s, ?_⟩
      simp only [Category.assoc]
      rw [show pullback.fst (s ≫ f) y ≫ s ≫ f = pullback.snd (s ≫ f) y ≫ y from pullback.condition]

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEqTopOfStableOfIsFractionRing
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory


open KaehlerDifferential in
theorem _root_.GlobalTheory.span_eq_top_of_stable_of_isFractionRing :
    ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k K] [Algebra F K] [FiniteDimensional F K] (B : Subalgebra k K) [IsFractionRing B K] (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Submodule.span K S = ⊤ → Submodule.span F S = ⊤ := by
  intro k F K _ _ _ _ _ _ B _ W _ _ _ _ S hS hspan
  set M := Submodule.span F S with hM
  let T : Subalgebra F K :=
    { carrier := {y | ∀ m ∈ M, y • m ∈ M}
      mul_mem' := fun {a b} ha hb m hm => by rw [mul_smul]; exact ha _ (hb m hm)
      one_mem' := fun m hm => by rwa [one_smul]
      add_mem' := fun {a b} ha hb m hm => by rw [add_smul]; exact M.add_mem (ha m hm) (hb m hm)
      zero_mem' := fun m _ => by rw [zero_smul]; exact M.zero_mem
      algebraMap_mem' := fun f m hm => by rw [algebraMap_smul]; exact M.smul_mem f hm }
  have hmemT : ∀ y : K, y ∈ T ↔ ∀ m ∈ M, y • m ∈ M := fun y => Iff.rfl
  have hB : ∀ c ∈ B, (c : K) ∈ T := by
    intro c hc m hm
    induction hm using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span (hS c hc s hs)
    | zero => rw [smul_zero]; exact M.zero_mem
    | add v w _ _ hv hw => rw [smul_add]; exact M.add_mem hv hw
    | smul f v _ hv => rw [smul_comm]; exact M.smul_mem f hv
  have hinv : ∀ y : K, y ∈ T → y⁻¹ ∈ T := by
    intro y hy
    exact T.inv_mem_of_algebraic (x := ⟨y, hy⟩) (Algebra.IsAlgebraic.isAlgebraic y)
  have hall : ∀ y : K, y ∈ T := by
    intro y
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := B) y
    rw [div_eq_mul_inv]
    exact T.mul_mem (hB _ a.2) (hinv _ (hB _ b.2))
  let MK : Submodule K W :=
    { carrier := M
      add_mem' := M.add_mem
      zero_mem' := M.zero_mem
      smul_mem' := fun c m hm => hall c m hm }
  have hle : Submodule.span K S ≤ MK := Submodule.span_le.mpr fun s hs => Submodule.subset_span hs
  rw [hspan] at hle
  exact eq_top_iff.mpr fun w _ => hle Submodule.mem_top

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapSmoothSurjectiveOfIsSeparable
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC
namespace GlobalTheory

theorem spec_map_smooth_surjective_of_isSeparable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] : Smooth (Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧ Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  have hfp : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  have : Algebra.Etale K L := ⟨inferInstance, inferInstance⟩
  have hs : Algebra.Smooth K L := inferInstance
  constructor
  · rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    rw [RingHom.Smooth]
    simp only [CommRingCat.hom_ofHom]
    exact RingHom.smooth_algebraMap.mpr hs
  · constructor
    intro x
    obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
    exact ⟨y, Subsingleton.elim _ _⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonPicEtaleLocalizationUnitsModuloStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_pic_etale_localization_unitsModulo : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], Subsingleton (CommRing.Pic (Localization (Algebra.algebraMapSubmonoid A' ((IsUnit.submonoid (B ⧸ Ideal.span {f})).comap (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f)))) := by
  first | (exact @GlobalTheory.PicLoc.subsingleton_pic_localization) | (exact GlobalTheory.PicLoc.subsingleton_pic_localization) | (intros; apply GlobalTheory.PicLoc.subsingleton_pic_localization <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyClassDiesOnLocalizationAwayStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_class_dies_on_localizationAway : B1 → ∀ (q : ℕ) (A : Type) [CommRing A] (M : Submonoid A) (n i : ℤ), IsUnit (q : A) → ∀ m ∈ M, ∀ y : Ht q (sp (Localization.Away m)) n i, ∀ φ : Localization.Away m →+* Localization M, φ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap φ) _ _ y = 0 → ∃ m' ∈ M, ∀ ψ : Localization.Away m →+* Localization.Away (m * m'), ψ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ψ) _ _ y = 0 := by
  first | (exact @GlobalTheory.EtC.AwayCont.kill_of_loc) | (exact GlobalTheory.EtC.AwayCont.kill_of_loc) | (intros; apply GlobalTheory.EtC.AwayCont.kill_of_loc <;> assumption)
end

