module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PlaceData
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.EtOfRestrict
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ)
open UpperTheory.Gal UpperTheory.Gal.Mod UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Mod.BaseChangeExamples

private theorem isUnit_nat {k : Type} [Field k] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) (m : ℕ)
    (h : (m : k) ≠ 0) : IsUnit (m : Γ(X, ⊤)) := by
  have := (h.isUnit).map ((q.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  simpa using this

private theorem isWt_one {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Etale p] : TranscendenceTraces.IsWt p (Wt.const Z 1) := by
  have h := TranscendenceTraces.multBasic_holds.2.2 p
  rw [← h]
  exact TranscendenceTraces.wtFlat_holds p

private theorem et_of_pb {A B C D : Scheme.{0}} {u : A ⟶ B} {s : A ⟶ C} {p : B ⟶ D} {e : C ⟶ D}
    (h : IsPullback u s p e) [Etale p] : Etale s :=
  MorphismProperty.of_isPullback (P := @Etale) h ‹_›

private theorem et_of_restrict {A B C D : Scheme.{0}} {u : A ⟶ B} {s : A ⟶ C} {p : B ⟶ D} {e : C ⟶ D}
    (h : IsPullback u s p e) (f : Γ(D, ⊤)) (hf : IsUnit (e.appTop f)) (he : Etale (p ∣_ D.basicOpen f)) : Etale s := by
  have hr : Set.range e ⊆ Set.range (D.basicOpen f).ι := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ e ⁻¹ᵁ D.basicOpen f := by
      rw [Scheme.preimage_basicOpen]
      have : C.basicOpen ((e.app ⊤).hom f) = ⊤ := Scheme.basicOpen_of_isUnit _ hf
      rw [this]; trivial
    rw [Scheme.Opens.range_ι]
    exact hx
  let e' : C ⟶ (D.basicOpen f).toScheme := IsOpenImmersion.lift _ e hr
  have he' : e' ≫ (D.basicOpen f).ι = e := IsOpenImmersion.lift_fac _ _ _
  have hq := isPullback_morphismRestrict p (D.basicOpen f)
  have hw : (s ≫ e') ≫ (D.basicOpen f).ι = u ≫ p := by
    rw [Category.assoc, he', h.w]
  let t := hq.lift (s ≫ e') u hw
  have ht1 : t ≫ (p ∣_ D.basicOpen f) = s ≫ e' := hq.lift_fst _ _ _
  have ht2 : t ≫ (p ⁻¹ᵁ D.basicOpen f).ι = u := hq.lift_snd _ _ _
  have hpb : IsPullback t s (p ∣_ D.basicOpen f) e' := by
    refine IsPullback.of_right (h₁₂ := (p ⁻¹ᵁ D.basicOpen f).ι) (h₂₂ := (D.basicOpen f).ι) (v₁₃ := p) ?_ ht1 hq.flip
    rw [ht2, he']
    exact h
  exact et_of_pb hpb

end UpperTheory.Gal.Mod.BaseChangeExamples

open UpperTheory.Gal.Mod.BaseChangeExamples in
theorem UpperTheory.Gal.Mod.bcEx :
    BCEx := by
  intro p O k Ω _ _ _ _ _ hp Y g T hg
  let q := pullback.snd g (sp (algebraMap O k))
  let s : geom Ω q ⟶ Y := pullback.fst _ _ ≫ pullback.fst _ _
  have h : IsPullback (pullback.fst T.p s) (pullback.snd T.p s) T.p s := IsPullback.of_hasPullback T.p s
  have hfin : IsFinite (pullback.snd T.p s) := by
    have := T.fin
    infer_instance
  have het : Etale (pullback.snd T.p s) :=
    et_of_restrict h (p : Γ(Y, ⊤)) (by simpa using isUnit_nat (pullback.fst q (sp (algebraMap k Ω)) ≫ q) p hp) T.et
  have c1 : (pullback.fst T.p s ≫ T.r) ≫ g =
      (pullback.snd T.p s ≫ pullback.fst q (sp (algebraMap k Ω)) ≫ q) ≫ sp (algebraMap O k) := by
    have e1 : pullback.fst T.p s ≫ T.p = pullback.snd T.p s ≫ s := h.w
    have e2 : pullback.fst g (sp (algebraMap O k)) ≫ g = q ≫ sp (algebraMap O k) := pullback.condition
    rw [Category.assoc, hg, reassoc_of% e1]
    simp only [s, Category.assoc, e2]
  let a : pullback T.p s ⟶ pullback g (sp (algebraMap O k)) :=
    pullback.lift (pullback.fst T.p s ≫ T.r) (pullback.snd T.p s ≫ pullback.fst q (sp (algebraMap k Ω)) ≫ q) c1
  have ha1 : a ≫ pullback.fst g (sp (algebraMap O k)) = pullback.fst T.p s ≫ T.r := pullback.lift_fst _ _ _
  have ha2 : a ≫ q = pullback.snd T.p s ≫ pullback.fst q (sp (algebraMap k Ω)) ≫ q := pullback.lift_snd _ _ _
  have c2 : a ≫ q = (pullback.snd T.p s ≫ pullback.snd q (sp (algebraMap k Ω))) ≫ sp (algebraMap k Ω) := by
    have e3 : pullback.fst q (sp (algebraMap k Ω)) ≫ q = pullback.snd q (sp (algebraMap k Ω)) ≫ sp (algebraMap k Ω) :=
      pullback.condition
    rw [ha2, e3, Category.assoc]
  let b : pullback T.p s ⟶ geom Ω q := pullback.lift a (pullback.snd T.p s ≫ pullback.snd q (sp (algebraMap k Ω))) c2
  have hb1 : b ≫ pullback.fst q (sp (algebraMap k Ω)) = a := pullback.lift_fst _ _ _
  have hb2 : b ≫ pullback.snd q (sp (algebraMap k Ω)) = pullback.snd T.p s ≫ pullback.snd q (sp (algebraMap k Ω)) :=
    pullback.lift_snd _ _ _
  refine ⟨⟨pullback T.p s, pullback.snd T.p s, b, Wt.const _ 1, hfin, isWt_one _⟩, pullback.fst T.p s, h, ?_, hb2, rfl⟩
  change b ≫ pullback.fst q (sp (algebraMap k Ω)) ≫ pullback.fst g (sp (algebraMap O k)) = pullback.fst T.p s ≫ T.r
  rw [reassoc_of% hb1, ha1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PEsStep
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ)
open UpperTheory.Gal UpperTheory.Gal.Mod UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

private theorem mem_submodule_of_basis_matrix {L M : Type*} [Field L] [AddCommGroup M] [Module L M] {P : Submodule L M}
    {d : ℕ} (b : Module.Basis (Fin d) L P) (g : M →ₗ[L] M) (A : Matrix (Fin d) (Fin d) L)
    (hb : ∀ j, g (b j) = ∑ i, A i j • (b i : M)) : ∀ x ∈ P, g x ∈ P := by
  intro x hx
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : M) := by
    have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
    exact h.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx', map_sum]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  rw [map_smul, hb]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (b k).2))

private theorem aeval_matrix_eq_zero_of_aeval_zero_on_submodule {L M : Type*} [Field L] [AddCommGroup M] [Module L M] {P : Submodule L M}
    {d : ℕ} (b : Module.Basis (Fin d) L P) (g : M →ₗ[L] M) (A : Matrix (Fin d) (Fin d) L)
    (hb : ∀ j, g (b j) = ∑ i, A i j • (b i : M)) (Q : Polynomial L)
    (hQ : ∀ x ∈ P, Polynomial.aeval g Q x = 0) : Polynomial.aeval A Q = 0 := by
  have hP := mem_submodule_of_basis_matrix b g A hb
  have hmat : LinearMap.toMatrixAlgEquiv b (g.restrict hP) = A := by
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply]
    have h : g.restrict hP (b j) = ∑ k, A k j • b k := by
      apply Subtype.ext
      simp [LinearMap.restrict_apply, hb]
    rw [h, b.repr_sum_self]
  have hcoe : ∀ (Q' : Polynomial L) (y : P),
      ((Polynomial.aeval (g.restrict hP) Q' y : P) : M) = Polynomial.aeval g Q' y := by
    intro Q' y
    induction Q' using Polynomial.induction_on' with
    | add p q hp hq => simp [map_add (f := _), LinearMap.add_apply, hp, hq]
    | monomial k a =>
      simp only [Polynomial.aeval_monomial, Module.End.pow_restrict k hP, Module.End.mul_apply,
        Module.algebraMap_end_apply, LinearMap.restrict_apply, SetLike.val_smul]
  have h0 : Polynomial.aeval (g.restrict hP) Q = 0 := by
    ext y
    rw [hcoe]
    simpa using hQ y y.2
  rw [← hmat, Polynomial.aeval_algEquiv, AlgHom.comp_apply, h0, map_zero]

theorem UpperTheory.Gal.Mod.esStep :
    TowES → PlaceData → GrPass → ESStep := by
  intro hT hP hG E Ω _ _ _ _ _ l _ ι H θ hN dd ρ hcont hpc w hl n ϑ R hcong hroots A hA
  obtain ⟨ρ₀, ⟨b, hb⟩, hgr⟩ := hpc
  obtain ⟨C, p, f, hp, hpw, hnorm, hon, hC⟩ := hcong
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hP E Ω w A hA
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hinv : ∀ σ : Gal(Ω/E), ∀ x ∈ piece l H Ω (Qbar l) θ,
      galV l H Ω (Qbar l) σ x ∈ piece l H Ω (Qbar l) θ := by
    intro σ
    exact mem_submodule_of_basis_matrix b (galV l H Ω (Qbar l) σ) (ρ₀ σ : Matrix (Fin dd) (Fin dd) (Qbar l)) (hb σ)
  have key := fun σ hσA => hT l p f n hp (Ow w) (h6 p hpw) E (by exact_mod_cast hp.ne_zero)
    (by rw [← hnorm]; exact h3) Ω A h1 h2 (h5 l hl) (Qbar l) H θ hN C ϑ hC hinv σ hσA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · obtain ⟨hsA, hsv⟩ := h7 s hs
    have hM : Polynomial.aeval (ρ₀ s : Matrix (Fin dd) (Fin dd) (Qbar l))
        (Polynomial.X - 1 : Polynomial (Qbar l)) = 0 := by
      refine aeval_matrix_eq_zero_of_aeval_zero_on_submodule b (galV l H Ω (Qbar l) s) _ (hb s) _ (fun x hx => ?_)
      simp [(key s hsA x hx).1 hsv]
    have hM' := hG (G E Ω) (Qbar l) dd ρ₀ ρ hgr s _ hM
    simp only [map_sub, Polynomial.aeval_X, map_one, sub_eq_zero] at hM'
    exact Units.ext hM'
  · obtain ⟨hσA, hσv⟩ := h8 _ σ hσ
    rw [h4, hnorm] at hσv
    have hM : Polynomial.aeval (ρ₀ σ⁻¹ : Matrix (Fin dd) (Fin dd) (Qbar l))
        (crystallineComparison.heckePol (normV w) n ϑ) = 0 := by
      refine aeval_matrix_eq_zero_of_aeval_zero_on_submodule b (galV l H Ω (Qbar l) σ⁻¹) _ (hb σ⁻¹) _ (fun x hx => ?_)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← (key σ hσA x hx).2 hσv, crystallineComparison.heckePol, h4, hnorm, map_sum, LinearMap.sum_apply,
        Finset.sum_range (fun j => (Polynomial.aeval (galV l H Ω (Qbar l) σ⁻¹))
          (Polynomial.C ((-1) ^ j * ((p ^ f : ℕ) : Qbar l) ^ j.choose 2 * ϑ j) * Polynomial.X ^ (n - j)) x)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
        Module.algebraMap_end_apply, Module.End.pow_apply]
      congr 1
      push_cast [co]
      ring
    have hM' := hG (G E Ω) (Qbar l) dd ρ₀ ρ hgr σ⁻¹ _ hM
    obtain ⟨hϑ0, hpol⟩ := hroots
    have hQ : crystallineComparison.heckePol (normV w) n ϑ =
        Polynomial.C (ϑ 0) * Polynomial.map ι.symm.toRingHom (crystallineComparison.rootPol R) := by
      have h := congrArg (Polynomial.map ι.symm.toRingHom) hpol
      rw [Polynomial.map_map, Polynomial.map_mul, Polynomial.map_C] at h
      simpa using h
    rw [hQ, map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      smul_eq_zero] at hM'
    exact hM'.resolve_left hϑ0
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PGalEx
section
theorem UpperTheory.Gal.Mod.galEx : UpperTheory.Gal.Mod.GalEx := UpperTheory.Gal.G3.pGalClosD (UpperTheory.Gal.G3.pSplitsPts UpperTheory.Gal.G3.pIsoPts)
  (UpperTheory.Gal.G3.pOrdEx UpperTheory.Gal.G3.pOrdStep)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PGrPass
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ)
open UpperTheory.Gal UpperTheory.Gal.Mod UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Mod.BlockProjectionMultiplicative

variable {d : ℕ} {L : Type} [Field L]

private def blkPart (c : Fin d → ℕ) (M : Matrix (Fin d) (Fin d) L) : Matrix (Fin d) (Fin d) L :=
  fun i j => if c i = c j then M i j else 0

private theorem blkPart_add (c : Fin d → ℕ) (M N : Matrix (Fin d) (Fin d) L) :
    blkPart c (M + N) = blkPart c M + blkPart c N := by
  ext i j
  simp only [blkPart, Matrix.add_apply]
  split_ifs <;> simp

private theorem blkPart_smul (c : Fin d → ℕ) (a : L) (M : Matrix (Fin d) (Fin d) L) :
    blkPart c (a • M) = a • blkPart c M := by
  ext i j
  simp only [blkPart, Matrix.smul_apply]
  split_ifs <;> simp

private theorem blkPart_one (c : Fin d → ℕ) : blkPart c (1 : Matrix (Fin d) (Fin d) L) = 1 := by
  ext i j
  simp only [blkPart]
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.one_apply_ne h]; simp

private theorem blkPart_mul (c : Fin d → ℕ) {M N : Matrix (Fin d) (Fin d) L}
    (hM : M.BlockTriangular c) (hN : N.BlockTriangular c) :
    blkPart c (M * N) = blkPart c M * blkPart c N := by
  ext i j
  rw [Matrix.mul_apply]
  change (if c i = c j then (M * N) i j else 0) =
    ∑ k, (if c i = c k then M i k else 0) * (if c k = c j then N k j else 0)
  by_cases h : c i = c j
  · rw [if_pos h, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : c i = c k
    · have h2 : c k = c j := h1.symm.trans h
      rw [if_pos h1, if_pos h2]
    · rw [if_neg h1, zero_mul]
      rcases lt_or_gt_of_ne h1 with h3 | h3
      · have h4 : c j < c k := h ▸ h3
        rw [hN h4, mul_zero]
      · rw [hM h3, zero_mul]
  · rw [if_neg h]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : c i = c k
    · have h2 : ¬ c k = c j := fun e => h (h1.trans e)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

private theorem blkTri_pow (c : Fin d → ℕ) {M : Matrix (Fin d) (Fin d) L}
    (hM : M.BlockTriangular c) (n : ℕ) : (M ^ n).BlockTriangular c := by
  induction n with
  | zero => rw [pow_zero]; exact Matrix.blockTriangular_one
  | succ n ih => rw [pow_succ]; exact ih.mul hM

private theorem blkPart_pow (c : Fin d → ℕ) {M : Matrix (Fin d) (Fin d) L}
    (hM : M.BlockTriangular c) (n : ℕ) : blkPart c (M ^ n) = blkPart c M ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, blkPart_one]
  | succ n ih => rw [pow_succ, pow_succ, blkPart_mul c (blkTri_pow c hM n) hM, ih]

private theorem blkPart_aeval (c : Fin d → ℕ) {M : Matrix (Fin d) (Fin d) L}
    (hM : M.BlockTriangular c) (P : Polynomial L) :
    blkPart c (Polynomial.aeval M P) = Polynomial.aeval (blkPart c M) P := by
  refine Polynomial.induction_on' P (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add (f := _), map_add (f := _), blkPart_add, hp, hq]
  · rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def,
      blkPart_smul, blkPart_pow c hM]

end UpperTheory.Gal.Mod.BlockProjectionMultiplicative

open UpperTheory.Gal.Mod.BlockProjectionMultiplicative in
theorem UpperTheory.Gal.Mod.grPass :
    GrPass := by
  intro Γ L _ _ d ρ₀ ρ hG g P h0
  obtain ⟨c, hc⟩ := hG
  obtain ⟨hT, hD⟩ := hc g
  have e : (ρ g : Matrix (Fin d) (Fin d) L) = blkPart c (ρ₀ g : Matrix (Fin d) (Fin d) L) := by
    ext i j
    exact hD i j
  rw [e, ← blkPart_aeval c hT, h0]
  ext i j
  simp [blkPart]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PLiesOp
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ gp fib IsWt)
open UpperTheory.Gal UpperTheory.Gal.Mod UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Mod.LiesOverOperations

private theorem unit_nat {k : Type} [Field k] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) (m : ℕ)
    (h : IsUnit (m : k)) : IsUnit (m : Γ(X, ⊤)) := by
  have := h.map ((q.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  simpa using this

private theorem wt_one {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Etale p] : IsWt p (Wt.const Z 1) := by
  rw [← TranscendenceTraces.multBasic_holds.2.2 p]
  exact TranscendenceTraces.wtFlat_holds p

private theorem pq_comp (l : ℕ) [Fact l.Prime] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = pullHQ l f n i ∘ₗ pullHQ l g n i := by
  unfold pullHQ; rw [pullHl_comp]; exact LinearMap.baseChange_comp _ _

private theorem pq_id (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) : pullHQ l (𝟙 E) n i = LinearMap.id := by
  unfold pullHQ; rw [pullHl_id]; exact LinearMap.baseChange_id

section Geo
variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]

private theorem geo_fst {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    (hu : u ≫ q = p) : geomMap Ω p u hu ≫ pullback.fst _ _ = pullback.fst _ _ ≫ u := pullback.lift_fst _ _ _

private theorem geo_snd {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    (hu : u ≫ q = p) : geomMap Ω p u hu ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

private theorem geo_pb {X Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of k)) (s : X ⟶ Y) :
    IsPullback (pullback.fst (s ≫ q) (sp (algebraMap k Ω))) (geomMap Ω (s ≫ q) s rfl) s
      (pullback.fst q (sp (algebraMap k Ω))) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd q (sp (algebraMap k Ω))) (v₂₂ := q) (h₃₁ := sp (algebraMap k Ω)) ?_
    (geo_fst Ω _ _ _).symm (IsPullback.of_hasPullback q _)
  rw [geo_snd]
  exact IsPullback.of_hasPullback _ _

end Geo

private theorem card_fib {A B C D : Scheme.{0}} {a : A ⟶ C} {v : A ⟶ B} {u : C ⟶ D} {b : B ⟶ D}
    (h : IsPullback a v u b) {Ω : Type} [Field Ω] (x : gp Ω ⟶ B) : (fib v x).ncard = (fib u (x ≫ b)).ncard := by
  have himg : fib u (x ≫ b) = (fun z => z ≫ a) '' fib v x := by
    ext y
    constructor
    · intro hy
      have hy' : y ≫ u = x ≫ b := hy
      exact ⟨h.lift y x hy', h.lift_snd _ _ _, h.lift_fst _ _ _⟩
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ≫ v = x := hz
      change (z ≫ a) ≫ u = x ≫ b
      rw [Category.assoc, h.w, reassoc_of% hz']
  rw [himg]
  symm
  apply Set.InjOn.ncard_image
  intro z hz z' hz' hzz
  have e1 : z ≫ v = x := hz
  have e2 : z' ≫ v = x := hz'
  exact h.hom_ext hzz (e1.trans e2.symm)

private theorem gen_ext {O k Ω : Type} [CommRing O] [Field k] [Algebra O k] [Field Ω] [Algebra k Ω] {Y A : Scheme.{0}}
    (g : Y ⟶ Spec (CommRingCat.of O)) (a b : A ⟶ geom Ω (pullback.snd g (sp (algebraMap O k))))
    (h1 : a ≫ pullback.fst _ _ ≫ pullback.fst _ _ = b ≫ pullback.fst _ _ ≫ pullback.fst _ _)
    (h2 : a ≫ pullback.snd _ _ = b ≫ pullback.snd _ _) : a = b := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using h1
    · have e : pullback.fst (pullback.snd g (sp (algebraMap O k))) (sp (algebraMap k Ω)) ≫ pullback.snd g (sp (algebraMap O k)) =
          pullback.snd _ _ ≫ sp (algebraMap k Ω) := pullback.condition
      rw [Category.assoc, Category.assoc, e, ← Category.assoc, h2, Category.assoc]
  · exact h2

end UpperTheory.Gal.Mod.LiesOverOperations

open UpperTheory.Gal.Mod.LiesOverOperations in
theorem UpperTheory.Gal.Mod.liesOp :
    HopOp → OpCover → LiesOp := by
  intro hHop hOC
  unfold LiesOp
  intro l _ p k L _ _ H θ O _ _ C Ω _ _ hl T g d m hF hLies c hBC
  obtain ⟨-, κ, h, hκt, hw⟩ := hLies
  obtain ⟨v, hvpb, hvf, hvb, hvw⟩ := hBC
  haveI := c.fin
  haveI : IsFinite (H.s g) := hF.1
  haveI : Etale (H.s g) := hF.2.1
  haveI : IsFinite (pullback.lift (H.s g) κ h) := hw.1
  let π := piG C Ω
  have hπs : π ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst H.q (sp (algebraMap k Ω)) ≫ C.π := by
    change geomMap Ω H.q (pullback.lift C.π H.q C.ov) (pullback.lift_snd _ _ _) ≫ _ ≫ _ = _
    rw [reassoc_of% (geo_fst Ω H.q (pullback.lift C.π H.q C.ov) (pullback.lift_snd _ _ _))]
    erw [pullback.lift_fst]
  have hπb : π ≫ pullback.snd _ _ = pullback.snd _ _ := geo_snd Ω _ _ _
  have P₁ := IsPullback.of_hasPullback c.p π
  have ha : (pullback.snd c.p π ≫ pullback.fst H.q (sp (algebraMap k Ω))) ≫ C.π = (pullback.fst c.p π ≫ v) ≫ T.p := by
    rw [Category.assoc, ← hπs, Category.assoc, hvpb.w, ← Category.assoc _ c.p, pullback.condition, Category.assoc]
  let a : pullback c.p π ⟶ pullback C.π T.p := pullback.lift _ _ ha
  have P₂ : IsPullback (a ≫ pullback.snd _ _) (pullback.snd c.p π) T.p (pullback.fst H.q (sp (algebraMap k Ω)) ≫ C.π) := by
    have := P₁.paste_horiz hvpb
    rw [hπs] at this
    rwa [show a ≫ pullback.snd _ _ = pullback.fst c.p π ≫ v from pullback.lift_snd _ _ _]
  have P₃ : IsPullback a (pullback.snd c.p π) (pullback.fst C.π T.p) (pullback.fst H.q (sp (algebraMap k Ω))) :=
    IsPullback.of_right P₂ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback C.π T.p).flip
  have hfY : pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω)) ≫ H.s g = H.sΩ Ω g ≫ pullback.fst _ _ :=
    (geo_fst Ω _ _ _).symm
  have hu : (pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω)) ≫ pullback.lift (H.s g) κ h) ≫ pullback.fst C.π T.p =
      H.sΩ Ω g ≫ pullback.fst H.q (sp (algebraMap k Ω)) := by
    rw [Category.assoc, pullback.lift_fst, hfY]
  let u : geom Ω (H.s g ≫ H.q) ⟶ pullback c.p π := P₃.lift _ _ hu
  have hua : u ≫ a = pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω)) ≫ pullback.lift (H.s g) κ h := P₃.lift_fst _ _ _
  have hus : u ≫ pullback.snd c.p π = H.sΩ Ω g := P₃.lift_snd _ _ _
  have P₄ : IsPullback (pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω))) u (pullback.lift (H.s g) κ h) a := by
    refine IsPullback.of_bot ?_ hua.symm P₃
    rw [hus, pullback.lift_fst]
    exact geo_pb Ω H.q (H.s g)
  have hav : a ≫ pullback.snd _ _ = pullback.fst c.p π ≫ v := pullback.lift_snd _ _ _
  have hlS : IsUnit (l : Γ(H.geomZ Ω, ⊤)) := unit_nat (pullback.snd H.q _) l hl
  have hl₀ := unit_nat (pullback.snd (pullback.snd C.p (sp (algebraMap O k))) (sp (algebraMap k Ω))) l hl
  have hsF : IsFinite (H.sΩ Ω g) := MorphismProperty.of_isPullback (P := @IsFinite) (geo_pb Ω H.q (H.s g)) ‹_›
  have hsE : Etale (H.sΩ Ω g) := MorphismProperty.of_isPullback (P := @Etale) (geo_pb Ω H.q (H.s g)) ‹_›
  have hwt₁ : IsWt (pullback.snd c.p π) (Wt.const _ 1) := by
    have := TranscendenceTraces.all_holds.1.1 (pullback.fst c.p π) (pullback.snd c.p π) c.p π c.w P₁ c.wt
    rw [hvw] at this
    exact this
  let c₁ : TranscendenceTraces.Corr (H.geomZ Ω) (geom Ω (pullback.snd C.p (sp (algebraMap O k)))) :=
    ⟨pullback c.p π, pullback.snd _ _, pullback.fst _ _ ≫ c.f, Wt.const _ 1, inferInstance, hwt₁⟩
  let c₂ : TranscendenceTraces.Corr (H.geomZ Ω) (geom Ω (pullback.snd C.p (sp (algebraMap O k)))) :=
    ⟨geom Ω (H.s g ≫ H.q), H.sΩ Ω g, H.tΩ Ω g ≫ π, Wt.const _ 1, hsF, wt_one _⟩
  have huF : IsFinite u := MorphismProperty.of_isPullback (P := @IsFinite) P₄ ‹_›
  have e₁ : u ≫ pullback.fst c.p π ≫ v = pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω)) ≫ κ := by
    rw [← hav, ← Category.assoc, hua, Category.assoc, pullback.lift_snd]
  have e₂ : u ≫ pullback.fst c.p π ≫ c.p = H.sΩ Ω g ≫ π := by
    rw [pullback.condition, ← Category.assoc, hus]
  have ht : H.tΩ Ω g ≫ pullback.fst H.q (sp (algebraMap k Ω)) = pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω)) ≫ H.t g :=
    geo_fst Ω _ _ _
  have htb : H.tΩ Ω g ≫ pullback.snd H.q (sp (algebraMap k Ω)) = pullback.snd _ _ := geo_snd Ω _ _ _
  have hsb : H.sΩ Ω g ≫ pullback.snd H.q (sp (algebraMap k Ω)) = pullback.snd _ _ := geo_snd Ω _ _ _
  have huf : u ≫ c₁.f = c₂.f := by
    change u ≫ pullback.fst c.p π ≫ c.f = H.tΩ Ω g ≫ π
    apply gen_ext C.p
    · simp only [Category.assoc]
      rw [hvf, hπs, reassoc_of% e₁, hκt, reassoc_of% ht]
    · simp only [Category.assoc]
      rw [hvb, reassoc_of% e₂, hπb, hsb, htb]
  have hcnt : ∀ (Ω' : Type) [Field Ω'] [IsAlgClosed Ω'] (x : gp Ω' ⟶ c₁.Z), (fib u x).ncard = m := by
    intro Ω' _ _ x
    rw [card_fib P₄ x]
    exact (Nat.card_coe_set_eq _).symm.trans (hw.2.2 Ω' (x ≫ a))
  have hcov : ∀ n : ℤ, c₂.opQ l n 0 = (m : ℚ_[l]) • c₁.opQ l n 0 := fun n =>
    @hOC l _ _ _ c₂ c₁ u huF m rfl rfl hus huf hlS hcnt n 0
  have hbc : ∀ n : ℤ, pullHQ l (sch.map π) n 0 ∘ₗ c.opQ l n 0 = c₁.opQ l n 0 := fun n => by
    have := TranscendenceTraces.adic.2.2.2.2.2.2.1 l n 0 c₁ c π (𝟙 _) (pullback.fst c.p π) P₁ (Category.comp_id _)
      (by rw [hvw]; rfl) hl₀
    rw [this, CategoryTheory.Functor.map_id, pq_id]
    rfl
  have key : ∀ (n : ℤ) x, trHQ l (H.sΩ Ω g) (Wt.const _ 1) n 0 (pullHQ l (sch.map (H.tΩ Ω g)) n 0 (pullHQ l (sch.map π) n 0 x)) =
      (m : ℚ_[l]) • pullHQ l (sch.map π) n 0 (c.opQ l n 0 x) := fun n x => by
    have h₁ := LinearMap.congr_fun (hcov n) x
    have h₂ := LinearMap.congr_fun (hbc n) x
    rw [LinearMap.comp_apply] at h₂
    rw [h₂, LinearMap.smul_apply] at *
    rw [← h₁]
    change _ = trHQ l (H.sΩ Ω g) (Wt.const _ 1) n 0 (pullHQ l (sch.map (H.tΩ Ω g ≫ π)) n 0 x)
    rw [Functor.map_comp, pq_comp]
    rfl
  rw [hHop l k H Ω hl g d hF]
  refine DirectSum.linearMap_ext _ fun n => LinearMap.ext fun x => ?_
  unfold pullTot
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, DirectSum.lmap_lof]
  rw [key n x, map_smul]
end

