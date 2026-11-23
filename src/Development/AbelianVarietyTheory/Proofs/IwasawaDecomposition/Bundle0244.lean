module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentSemilinearOfBasis
section
noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem linearIndependent_semilinear_of_basis {K : Type} [Field K] (e : K →+* ℂ) {V : Type} [AddCommGroup V]
    [Module K V] {W : Type} [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[e] W) {ι κ : Type}
    (b : Module.Basis ι K V) (hb : LinearIndependent ℂ (fun i => j (b i))) (v : κ → V)
    (hv : LinearIndependent K v) : LinearIndependent ℂ (fun i => j (v i)) := by
  classical
  set S : Submodule ℂ W := Submodule.span ℂ (Set.range fun i => j (b i)) with hS
  have hmem : ∀ x, j x ∈ S := by
    intro x
    have hx : x ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact S.add_mem hy hz
    | smul a y _ hy => rw [map_smulₛₗ]; exact S.smul_mem _ hy
  let j' : V →ₛₗ[e] S := j.codRestrict S hmem
  have h1 : LinearIndependent ℂ (fun i => j' (b i)) :=
    LinearIndependent.of_comp S.subtype hb
  have h2 : Submodule.span ℂ (Set.range fun i => j' (b i)) = ⊤ := by
    apply Submodule.map_injective_of_injective S.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    rfl
  let b' := Module.Basis.extend (hv.linearIndepOn_id)
  have h3 := (GlobalTheory.semilinear_basis_image_indep_of_basis K e V S j' ι _ b b' ⟨h1, h2⟩).1
  have h4 := h3.map' S.subtype S.ker_subtype
  let f : κ → (hv.linearIndepOn_id).extend (Set.subset_univ _) := fun i =>
    ⟨v i, (hv.linearIndepOn_id).subset_extend _ ⟨i, rfl⟩⟩
  have hf : Function.Injective f := fun a c h => hv.injective (congrArg Subtype.val h)
  have h5 := h4.comp f hf
  have h6 : (fun i => j (v i)) = (⇑S.subtype ∘ fun i => j' (b' i)) ∘ f := by
    funext i
    simp [b', f, j', Module.Basis.extend_apply_self]
  rw [h6]
  exact h5

def coordForm {K : Type} [Field K] (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (c : Fin n → W) : (Fin n → K) →ₛₗ[e] W where
  toFun x := ∑ i, e (x i) • c i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, mul_smul]

theorem coordForm_basisFun {K : Type} [Field K] (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (c : Fin n → W) (i : Fin n) : coordForm e c (Pi.basisFun K (Fin n) i) = c i := by
  classical
  show ∑ k, e (Pi.basisFun K (Fin n) i k) • c k = c i
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · simp

def ramForm {B : Base} {C : Cols B} (W : RowsRest B C) (u : B.Word) :
    (C.fm u).ramSub →ₛₗ[B.embLL] W.Mu u where
  toFun x := (W.eMu u).symm ⟨(C.fm u).emb 0 x, x.2⟩
  map_add' x y := by
    rw [← map_add (f := _)]; congr 1; ext1; simp
  map_smul' a x := by
    rw [← map_smul]; congr 1; ext1; simp [map_smulₛₗ]

theorem eMu_ramForm {B : Base} {C : Cols B} (W : RowsRest B C) (u : B.Word) (x : (C.fm u).ramSub) :
    ((W.eMu u (ramForm W u x) : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) =
      (C.fm u).emb 0 x := by
  show ((W.eMu u ((W.eMu u).symm _) : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) = _
  rw [LinearEquiv.apply_symm_apply]

theorem ramForm_basis {B : Base} {C : Cols B} (W : RowsRest B C) (u : B.Word) {κ : Type}
    (b : Module.Basis κ B.LL (C.fm u).ramSub) :
    LinearIndependent ℂ (fun i => ramForm W u (b i)) ∧
      Submodule.span ℂ (Set.range (fun i => ramForm W u (b i))) = ⊤ := by
  let g : W.Mu u →ₗ[ℂ] ((C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) :=
    (C.mem u).A.Mram.subtype ∘ₗ (W.eMu u).toLinearMap
  have hg : ∀ x, g (ramForm W u x) = (C.fm u).emb 0 x := eMu_ramForm W u
  have hginj : Function.Injective g := (C.mem u).A.Mram.injective_subtype.comp (W.eMu u).injective
  constructor
  · apply LinearIndependent.of_comp g
    have := linearIndependent_semilinear_of_basis B.embLL ((C.fm u).emb 0) ((C.fm u).lat 0).b
      ((C.fm u).emb_basis 0).1 (fun i => ((b i : (C.fm u).ramSub) : ((C.fm u).lat 0).V))
      (b.linearIndependent.map' (C.fm u).ramSub.subtype (Submodule.ker_subtype _))
    have h6 : (⇑g ∘ fun i => ramForm W u (b i)) =
        fun i => (C.fm u).emb 0 ((b i : (C.fm u).ramSub) : ((C.fm u).lat 0).V) := funext fun i => hg _
    rw [h6]
    exact this
  · set S := Submodule.span ℂ (Set.range (fun i => ramForm W u (b i))) with hS
    have hmem : ∀ x, ramForm W u x ∈ S := by
      intro x
      have hx : x ∈ Submodule.span B.LL (Set.range b) := by rw [b.span_eq]; trivial
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add y z _ _ hy hz => rw [map_add (f := _)]; exact S.add_mem hy hz
      | smul a y _ hy => rw [map_smulₛₗ]; exact S.smul_mem _ hy
    rw [eq_top_iff]
    intro φ _
    have h1 : g φ ∈ (C.mem u).A.Mram := (W.eMu u φ).2
    rw [← GlobalTheory.RamRational.span_ramSub_cols B C u] at h1
    have h2 : Submodule.span ℂ ((C.fm u).emb 0 '' ((C.fm u).ramSub : Set ((C.fm u).lat 0).V)) ≤ S.map g := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨_, hmem ⟨x, hx⟩, hg _⟩
    obtain ⟨ψ, hψ, hψ'⟩ := h2 h1
    rwa [← hginj hψ']

theorem exists_divStage (B : Base) (C : Cols B) (W : RowsRest B C) (n : ℕ) (c : Module.Basis (Fin n) ℂ W.EE)
    (Xo : InfinitePlace B.LL → Matrix (Fin n) (Fin n) ℂ) (hXo : ∀ v, IsUnit (Xo v).det)
    (Lr : Submodule (𝓞 B.LL) (Fin n → B.LL)) (Ln : ∀ u, Submodule (𝓞 B.LL) ((C.fm u).lat 0).V)
    (Bk : ∀ u, ((C.fm u).lat 0).V →ₗ[B.LL] Module.Dual B.LL (Fin n → B.LL)) (h : B.Word → ℝ) (etaF : ℝ) :
    ∃ (V : DivStage B C W) (e : V.div.RR.V ≃ₗ[B.LL] (Fin n → B.LL)),
      (∀ x, V.jEE x = ∑ i, B.embLL (e x i) • c i) ∧ (∀ x, x ∈ V.div.RR.L ↔ e x ∈ Lr) ∧
      (∀ v, v ≠ InfinitePlace.mk B.embLL → ∀ x, Formalism.HermitianLatticesTheory.normAt V.div.RR.b V.div.RR.X v x =
        Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin n)) Xo v (e x)) ∧
      (∀ u x, x ∈ (V.div.Nu u).L ↔ V.nuIn u x ∈ Ln u) ∧
      (∀ u φ x, V.div.Bk u φ x = Bk u (V.nuIn u φ) (e x)) ∧ V.div.h = h ∧ V.div.etaF = etaF ∧
      V.div.HH = sFrame V.div.Nu V.div.h + V.div.RR.muMax := by
  classical
  obtain ⟨X0, hX0, hX0n⟩ := GlobalTheory.exists_frames_normAt_eq_norm B.LL B.embLL W.EE n c Lr
  choose m bN XN hXN hXNn using fun u : B.Word =>
    GlobalTheory.Mem.exists_restricted_frames B.LL ((C.fm u).lat 0) (C.fm u).ramSub ⊥ ((C.fm u).lat_good 0).1
  let X : InfinitePlace B.LL → Matrix (Fin n) (Fin n) ℂ := fun v =>
    if v = InfinitePlace.mk B.embLL then X0 v else Xo v
  let RR : HLat B.LL :=
    { V := Fin n → B.LL, ι := Fin n, b := Pi.basisFun B.LL (Fin n), X := X, L := Lr }
  let Nu : B.Word → HLat B.LL := fun u =>
    { V := (C.fm u).ramSub, ι := Fin (m u), b := bN u, X := XN u,
      L := (Ln u).comap ((C.fm u).ramSub.subtype.restrictScalars (𝓞 B.LL)) }
  let D : DivData B.LL B.Word :=
    { RR := RR, Nu := Nu, Bk := fun u => (Bk u) ∘ₗ (C.fm u).ramSub.subtype, h := h,
      HH := sFrame Nu h + RR.muMax, HH_ge := le_rfl, etaF := etaF, Dall := W.Dall, delP := W.delp,
      delP_le_one := W.delp_le_one }
  let V : DivStage B C W :=
    { div := D
      div_good := ⟨fun v => by
        show IsUnit (if v = InfinitePlace.mk B.embLL then X0 v else Xo v).det
        split_ifs
        · exact hX0 v
        · exact hXo v, fun u v => hXN u v⟩
      jEE := coordForm B.embLL c
      jEE_basis := by
        have : (fun i => coordForm B.embLL c (Pi.basisFun B.LL (Fin n) i)) = c :=
          funext (coordForm_basisFun B.embLL c)
        show LinearIndependent ℂ (fun i => coordForm B.embLL c (Pi.basisFun B.LL (Fin n) i)) ∧
          Submodule.span ℂ (Set.range (fun i => coordForm B.embLL c (Pi.basisFun B.LL (Fin n) i))) = ⊤
        rw [this]
        exact ⟨c.linearIndependent, c.span_eq⟩
      jN := ramForm W
      jN_basis := fun u => ramForm_basis W u (bN u)
      Dall_eq := rfl
      delP_eq := rfl
      nuIn := fun u => (C.fm u).ramSub.subtype
      nuIn_inj := fun u => (C.fm u).ramSub.injective_subtype
      nuIn_range := fun u => Submodule.range_subtype _
      nuIn_jN := fun u x => eMu_ramForm W u x
      nuIn_norm := fun u v x => hXNn u v x
      jEE_norm := fun x => by
        refine Eq.trans ?_ (hX0n x)
        show Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin n)) X _ x = _
        simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, X, if_true] }
  refine ⟨V, LinearEquiv.refl _ _, fun x => rfl, fun x => Iff.rfl, fun v hv x => ?_, fun u x => Iff.rfl,
    fun u φ x => rfl, rfl, rfl, rfl⟩
  show Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin n)) X v x = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin n)) Xo v x
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, X, if_neg hv]

end GlobalTheory.Mem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompletionNorm

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem isEquiv_valued :
    (valuation (w.adicCompletion E)).IsEquiv
      (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))

theorem exists_unit_valued_eq :
    ∃ ϖ : (w.adicCompletion E)ˣ, Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1) := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  have h : Valued.v ((π : E) : w.adicCompletion E) = WithZero.exp (-1) := by
    rw [w.valuedAdicCompletion_eq_valuation']; exact hπ
  have h0 : ((π : E) : w.adicCompletion E) ≠ 0 := by
    intro h'; rw [h', map_zero] at h; exact WithZero.zero_ne_coe h
  exact ⟨Units.mk0 _ h0, h⟩

theorem le_exp_neg_one_of_lt_one {a : WithZero (Multiplicative ℤ)} (ha : a < 1) : a ≤ WithZero.exp (-1) := by
  by_cases h0 : a = 0
  · simp [h0]
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at ha
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega

theorem valued_eq_exp (x : (w.adicCompletion E)ˣ) :
    Valued.v (x : w.adicCompletion E) = WithZero.exp (-ord (w.adicCompletion E) x) := by
  have he := isEquiv_valued w
  obtain ⟨ϖ, hϖ⟩ := exists_unit_valued_eq w
  have hϖ1 : Valued.v (ϖ : w.adicCompletion E) < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hu : valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) = uniformizer (w.adicCompletion E) := by
    apply le_antisymm
    · exact le_uniformizer_iff.2 (he.lt_one_iff_lt_one.2 hϖ1)
    · obtain ⟨y, hy⟩ := valuation_surjective (uniformizer (w.adicCompletion E))
      rw [← hy]
      have hy1 : Valued.v y < 1 := he.lt_one_iff_lt_one.1 (hy ▸ uniformizer_lt_one)
      exact (he y ϖ).2 (hϖ ▸ le_exp_neg_one_of_lt_one hy1)
  have hord : ord (w.adicCompletion E) ϖ = 1 := SmGL.ord_eq_one hu
  let o : (w.adicCompletion E)ˣ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun x => .ofAdd (ord (w.adicCompletion E) x)) fun x y => by rw [SmGL.ord_mul, ofAdd_add]
  set n := ord (w.adicCompletion E) x
  set u := x * ϖ ^ (-n)
  have hou : o u = 1 := by
    rw [map_mul, map_zpow, show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd hord, ← ofAdd_zsmul,
      smul_eq_mul, mul_one]
    show Multiplicative.ofAdd n * Multiplicative.ofAdd (-n) = 1
    rw [← ofAdd_add, add_neg_cancel, ofAdd_zero]
  have hu1 : valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1 :=
    SmGL.ord_eq_zero_iff.1 (ofAdd_eq_one.1 hou)
  have hv1 : Valued.v (u : w.adicCompletion E) = 1 := he.eq_one_iff_eq_one.1 hu1
  have hx : x = u * ϖ ^ n := by simp [u]
  rw [hx, Units.val_mul, map_mul, hv1, one_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← WithZero.exp_zsmul,
    smul_eq_mul, mul_neg_one]

theorem normV_eq_absNorm : normV w = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem norm_eq_zpow (x : (w.adicCompletion E)ˣ) :
    ‖(x : w.adicCompletion E)‖ = ((normV w : ℕ) : ℝ) ^ (-ord (w.adicCompletion E) x) := by
  rw [FinitePlace.norm_def, valued_eq_exp, WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero (a := -ord (w.adicCompletion E) x)), WithZero.log_exp]
  simp [normV_eq_absNorm]

theorem one_lt_normV : 1 < normV w := by
  have := one_lt_resCard (w.adicCompletion E)
  rwa [GlobalTheory.LocLanglands.resCard_eq_normV] at this

theorem valuation_le_iff_norm_le (x y : w.adicCompletion E) :
    valuation (w.adicCompletion E) x ≤ valuation (w.adicCompletion E) y ↔ ‖x‖ ≤ ‖y‖ := by
  have h1 : (1 : NNReal) < (Ideal.absNorm w.asIdeal : NNReal) := by
    rw [← normV_eq_absNorm]; exact_mod_cast one_lt_normV w
  rw [isEquiv_valued w x y, FinitePlace.norm_def, FinitePlace.norm_def, NNReal.coe_le_coe]
  exact (WithZeroMulInt.toNNReal_strictMono h1).le_iff_le.symm

theorem range_map_eq_KO (m : ℕ) :
    (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype).range = KO (w.adicCompletion E) (Fin m) := by
  have he := isEquiv_valued w
  have hO : 𝒪[w.adicCompletion E] = (w.adicCompletionIntegers E).toSubring := by
    ext y
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
    exact Iff.rfl
  let e := RingEquiv.subringCongr hO
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨GeneralLinearGroup.map e.symm.toRingHom h, ?_⟩
    ext i j; rfl
  · rintro ⟨h, rfl⟩
    refine ⟨GeneralLinearGroup.map e.toRingHom h, ?_⟩
    ext i j; rfl

end GlobalTheory.CompletionNorm


open GlobalTheory.CompletionNorm in
theorem GlobalTheory.CompletionNorm.norm_nabs_valuation : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), (∀ x : (w.adicCompletion E)ˣ, ‖(x : w.adicCompletion E)‖ = nabs (w.adicCompletion E) x ∧ ‖(x : w.adicCompletion E)‖ = ((normV w : ℕ) : ℝ) ^ (-ord (w.adicCompletion E) x) ∧ Valued.v (x : w.adicCompletion E) = WithZero.exp (-ord (w.adicCompletion E) x)) ∧ (∀ x y : w.adicCompletion E, valuation (w.adicCompletion E) x ≤ valuation (w.adicCompletion E) y ↔ ‖x‖ ≤ ‖y‖) ∧ ∀ m : ℕ, (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype).range = KO (w.adicCompletion E) (Fin m) := by
  intro E _ _ w
  refine ⟨fun x => ⟨?_, norm_eq_zpow w x, valued_eq_exp w x⟩, valuation_le_iff_norm_le w, range_map_eq_KO w⟩
  let k := w.adicCompletion E
  have ord_pow (z : kˣ) (n : ℕ) : SmGL.ord k (z ^ n) = n * SmGL.ord k z := by
    induction n with
    | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_mul]
      exact SmGL.ord_eq_zero (by simp)
    | succ n ih =>
      rw [pow_succ, SmGL.ord_mul, ih]
      push_cast
      ring
  have hexists : ∃ ϖ : kˣ, SmGL.ord k ϖ = 1 ∧ nabs k ϖ = (resCard k : ℝ)⁻¹ := by
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (valuation k).integer
    have hp0 : (p : k) ≠ 0 := by
      intro h
      exact hp.ne_zero (Subtype.ext h)
    obtain ⟨y, hy⟩ : ∃ y : k, valuation k y = uniformizer k := valuation_surjective _
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, map_zero] at hy
      exact (uniformizer_pos (R := k)).ne hy
    have hyint : y ∈ (valuation k).integer := by
      rw [Valuation.mem_integer_iff, hy]
      exact uniformizer_lt_one.le
    obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨y, hyint⟩ : (valuation k).integer)) (fun h => hy0 (congrArg Subtype.val h)) hp
    have hu0 : ((u : (valuation k).integer) : k) ≠ 0 := by
      intro h
      exact u.ne_zero (Subtype.ext h)
    refine ⟨Units.mk0 (p : k) hp0, ?_, _root_.GlobalTheory.SplitWeil.nabs_uniformiser hp rfl⟩
    have hyo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 y hy0) = 1 :=
      _root_.GlobalTheory.SmGL.ord_eq_one hy
    have huo : _root_.GlobalTheory.SmGL.ord k (Units.mk0 _ hu0) = 0 := by
      apply _root_.GlobalTheory.SmGL.ord_eq_zero
      exact (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit
    have hsplit : Units.mk0 y hy0 = Units.mk0 _ hu0 * Units.mk0 (p : k) hp0 ^ m := by
      apply Units.ext
      have := congrArg Subtype.val hu
      simpa using this
    rw [hsplit, _root_.GlobalTheory.SmGL.ord_mul, huo, ord_pow,
      zero_add] at hyo
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hyo with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · omega
  have hnabs (x : kˣ) : nabs k x = (resCard k : ℝ) ^ (-SmGL.ord k x) := by
    obtain ⟨ϖ, hord, habs⟩ := hexists
    have hq : (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ≠ 0 := by
      have := _root_.GlobalTheory.SplitWeil.one_lt_resCard k
      positivity
    have hinv : _root_.GlobalTheory.SplitWeil.nabs k ϖ⁻¹ = _root_.GlobalTheory.SplitWeil.resCard k := by
      have h := _root_.GlobalTheory.SplitWeil.nabs_mul k ϖ ϖ⁻¹
      rw [mul_inv_cancel, _root_.GlobalTheory.SplitWeil.nabs_one, habs] at h
      exact ((inv_mul_eq_one₀ hq).mp h.symm).symm
    have oinv : _root_.GlobalTheory.SmGL.ord k ϖ⁻¹ = -1 := by
      have h := _root_.GlobalTheory.SmGL.ord_mul k ϖ ϖ⁻¹
      rw [mul_inv_cancel, hord,
        _root_.GlobalTheory.SmGL.ord_eq_zero (x := (1 : kˣ)) (by simp only [Units.val_one, map_one])] at h
      omega
    have key : ∀ m : ℤ, _root_.GlobalTheory.SplitWeil.nabs k (ϖ ^ m) =
        (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-m) ∧ _root_.GlobalTheory.SmGL.ord k (ϖ ^ m) = m := by
      intro m
      refine Int.induction_on m ?_ ?_ ?_
      · refine ⟨by simp [_root_.GlobalTheory.SplitWeil.nabs_one], ?_⟩
        rw [zpow_zero]
        exact _root_.GlobalTheory.SmGL.ord_eq_zero (by simp only [Units.val_one, map_one])
      · intro i ih
        rw [_root_.zpow_add_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
          ih.1, ih.2, habs, hord]
        refine ⟨?_, rfl⟩
        rw [neg_add, zpow_add₀ hq, _root_.zpow_neg_one]
      · intro i ih
        rw [_root_.zpow_sub_one, _root_.GlobalTheory.SplitWeil.nabs_mul, _root_.GlobalTheory.SmGL.ord_mul,
          ih.1, ih.2, hinv, oinv]
        refine ⟨?_, by ring⟩
        rw [show -(-(i : ℤ) - 1) = -(-(i : ℤ)) + 1 by ring, zpow_add₀ hq, _root_.zpow_one]
    set o := _root_.GlobalTheory.SmGL.ord k x
    have hy : _root_.GlobalTheory.SmGL.ord k (x * ϖ ^ (-o)) = 0 := by
      rw [_root_.GlobalTheory.SmGL.ord_mul, (key _).2]
      ring
    have hy1 : _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o)) = 1 :=
      _root_.GlobalTheory.SmGL.nabs_eq_one k
        (_root_.GlobalTheory.SmGL.ord_eq_zero_iff.mp hy)
    have hx : x * ϖ ^ (-o) * ϖ ^ o = x := by
      rw [mul_assoc, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]
    calc _root_.GlobalTheory.SplitWeil.nabs k x
        = _root_.GlobalTheory.SplitWeil.nabs k (x * ϖ ^ (-o) * ϖ ^ o) := by rw [hx]
      _ = (_root_.GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-o) := by
        rw [_root_.GlobalTheory.SplitWeil.nabs_mul, hy1, (key o).1, one_mul]
  rw [norm_eq_zpow, hnabs, GlobalTheory.LocLanglands.resCard_eq_normV]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjUnipotentBorel
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.UnipFlip

theorem longElt_conj_apply {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    ((longElt n R : Matrix (Fin n) (Fin n) R) * A * (longElt n R : Matrix (Fin n) (Fin n) R)) i j
      = A i.rev j.rev := by
  simp only [Matrix.mul_apply, longElt, Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro b _ hb; rw [if_neg]; intro e; exact hb (by rw [e, Fin.rev_rev])
  · simp

theorem inv_apply_succ {R : Type} [CommRing R] {n : ℕ} {u : GL (Fin n) R} (hu : u ∈ unipB R (Fin n))
    (p q : Fin n) (h : (q : ℕ) = p + 1) :
    ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p q = - (u : Matrix (Fin n) (Fin n) R) p q := by
  have hv : u⁻¹ ∈ unipB R (Fin n) := inv_mem hu
  rw [mem_unipB] at hu hv
  have hpq : p ≠ q := by intro e; subst e; omega
  have key := congrFun (congrFun (congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R)) (mul_inv_cancel u)) p) q
  simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_ne hpq] at key
  rw [Fintype.sum_eq_add p q hpq] at key
  · rw [hu.2 p, hv.2 q, one_mul, mul_one] at key
    linear_combination key
  · intro c ⟨hcp, hcq⟩
    rcases lt_or_gt_of_ne hcp with hlt | hgt
    · rw [hu.1 p c hlt, zero_mul]
    · have : q < c := by
        have h1 : (p : ℕ) < c := hgt
        have h2 : (c : ℕ) ≠ q := fun e => hcq (Fin.ext e)
        show (q : ℕ) < c
        omega
      rw [hv.1 c q this, mul_zero]

theorem longElt_invT_conj_unipB : ∀ (R : Type) [CommRing R] (n : ℕ) (u : GL (Fin n) R), u ∈ unipB R (Fin n) →
    longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R ∈ unipB R (Fin n) ∧
      superDiag (longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R) = -superDiag u := by
  intro R _ n u hu
  have hv : u⁻¹ ∈ unipB R (Fin n) := inv_mem hu
  have hval : ∀ i j : Fin n,
      ((longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j
        = ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j.rev i.rev := by
    intro i j
    rw [Units.val_mul, Units.val_mul]
    rw [longElt_conj_apply]
    rfl
  rw [mem_unipB] at hv
  refine ⟨?_, ?_⟩
  · rw [mem_unipB]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hval]; exact hv.1 _ _ (Fin.rev_lt_rev.2 hij)
    · rw [hval]; exact hv.2 _
  · simp only [superDiag, Finset.sum_filter]
    simp_rw [hval]
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv Fin.revPerm _ _ fun p => ?_
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv Fin.revPerm _ _ fun q => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev]

    have hiff : ((q.rev : Fin n) : ℕ) = (p.rev : ℕ) + 1 ↔ (p : ℕ) = q + 1 := by
      simp only [Fin.val_rev]; have := p.isLt; have := q.isLt; omega
    by_cases h : (p : ℕ) = q + 1
    · rw [if_pos h, if_pos (hiff.2 h), inv_apply_succ hu p.rev q.rev (hiff.2 h)]
    · rw [if_neg h, if_neg (mt hiff.1 h), neg_zero]

end GlobalTheory.UnipFlip
end
end

