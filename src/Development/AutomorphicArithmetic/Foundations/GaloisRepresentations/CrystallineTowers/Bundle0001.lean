module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.BcCover
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.GalV
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.G3

namespace UpperTheory.Gal.Seam

private theorem sq_up {A B A' B' S S' : Scheme.{0}} {f : A ⟶ B} {qB : B ⟶ S} {qA : A ⟶ S} (hA : f ≫ qB = qA) {g : S' ⟶ S}
    {fA : A' ⟶ A} {pA : A' ⟶ S'} (hA' : IsPullback fA pA qA g) {w : B' ⟶ B} {pB : B' ⟶ S'} (hB : IsPullback w pB qB g)
    {f' : A' ⟶ B'} (h1 : f' ≫ w = fA ≫ f) (h2 : f' ≫ pB = pA) : IsPullback fA f' f w := by
  subst hA; subst h2
  have s : IsPullback (f' ≫ pB) fA g (f ≫ qB) := hA'.flip
  exact (IsPullback.of_right s h1 hB.flip).flip

private abbrev spf {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : sp B ⟶ sp A := Spec.map (CommRingCat.ofHom f)

private theorem fEt_bc : FEtBasic := pFEtBasic pPtsOfSplits

private theorem splits_bc : SplitsBasic := pSplitsBasic (pSplitsPts pIsoPts) pPtsOfSplits

section

variable {k K O O' L : Type} [Field k] [Field K] [CommRing O] [CommRing O'] [Algebra O k] [Algebra O' K] [Field L]
  (τ : k →+* K) (φ : O →+* O')

private theorem gen_sq (hφ : ∀ x, algebraMap O' K (φ x) = τ (algebraMap O k x)) :
    gen O' K ≫ spf φ = spf τ ≫ gen O k := by
  simp only [gen, spf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact hφ x

variable {H : HTower k} {θ : H.Γ → L} (C : Cover H θ O) (hφ : ∀ x, algebraMap O' K (φ x) = τ (algebraMap O k x))

include hφ in
private theorem pullback_square_commutes : (pullback.fst H.q (spf τ) ≫ C.π) ≫ C.p = (pullback.snd H.q (spf τ) ≫ gen O' K) ≫ spf φ := by
  rw [Category.assoc, C.ov, Category.assoc, gen_sq τ φ hφ, ← Category.assoc, pullback.condition, Category.assoc]

private def piY : pullback H.q (spf τ) ⟶ pullback C.p (spf φ) :=
  pullback.lift (pullback.fst H.q (spf τ) ≫ C.π) (pullback.snd H.q (spf τ) ≫ gen O' K) (pullback_square_commutes τ φ C hφ)

private theorem piY_fst : piY τ φ C hφ ≫ pullback.fst C.p (spf φ) = pullback.fst H.q (spf τ) ≫ C.π := pullback.lift_fst _ _ _

private theorem piY_snd : piY τ φ C hφ ≫ pullback.snd C.p (spf φ) = pullback.snd H.q (spf τ) ≫ gen O' K := pullback.lift_snd _ _ _

private def wG : pullback (pullback.snd C.p (spf φ)) (gen O' K) ⟶ pullback C.p (gen O k) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ spf τ) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, gen_sq τ φ hφ])

private theorem wG_fst : wG τ φ C hφ ≫ pullback.fst C.p (gen O k) =
    pullback.fst (pullback.snd C.p (spf φ)) (gen O' K) ≫ pullback.fst C.p (spf φ) := pullback.lift_fst _ _ _

private theorem wG_snd : wG τ φ C hφ ≫ pullback.snd C.p (gen O k) =
    pullback.snd (pullback.snd C.p (spf φ)) (gen O' K) ≫ spf τ := pullback.lift_snd _ _ _

private theorem sqG : IsPullback (wG τ φ C hφ) (pullback.snd (pullback.snd C.p (spf φ)) (gen O' K))
    (pullback.snd C.p (gen O k)) (spf τ) := by
  have a := IsPullback.of_hasPullback (pullback.snd C.p (spf φ)) (gen O' K)
  have b := IsPullback.of_hasPullback C.p (spf φ)
  have c : IsPullback (pullback.fst (pullback.snd C.p (spf φ)) (gen O' K) ≫ pullback.fst C.p (spf φ))
      (pullback.snd (pullback.snd C.p (spf φ)) (gen O' K)) C.p (gen O' K ≫ spf φ) := a.paste_horiz b
  rw [gen_sq τ φ hφ, ← wG_fst τ φ C hφ] at c
  exact IsPullback.of_right c (wG_snd τ φ C hφ) (IsPullback.of_hasPullback C.p (gen O k))

private def piK' : pullback H.q (spf τ) ⟶ pullback (pullback.snd C.p (spf φ)) (gen O' K) :=
  pullback.lift (piY τ φ C hφ) (pullback.snd H.q (spf τ)) (piY_snd τ φ C hφ)

private theorem piK'_fst : piK' τ φ C hφ ≫ pullback.fst (pullback.snd C.p (spf φ)) (gen O' K) = piY τ φ C hφ := pullback.lift_fst _ _ _

private theorem piK'_snd : piK' τ φ C hφ ≫ pullback.snd (pullback.snd C.p (spf φ)) (gen O' K) = pullback.snd H.q (spf τ) :=
  pullback.lift_snd _ _ _

private theorem sqPi : IsPullback (pullback.fst H.q (spf τ)) (piK' τ φ C hφ) (piK C) (wG τ φ C hφ) := by
  refine sq_up (piK_snd C) (IsPullback.of_hasPullback H.q (spf τ)) (sqG τ φ C hφ) ?_ (piK'_snd τ φ C hφ)
  apply pullback.hom_ext
  · rw [Category.assoc, wG_fst, ← Category.assoc, piK'_fst, piY_fst, Category.assoc, pullback.lift_fst]
  · rw [Category.assoc, wG_snd, ← Category.assoc, piK'_snd, Category.assoc, piK_snd, pullback.condition]

private theorem a_q (δ : C.Δ) : C.a δ ≫ H.q = H.q := by
  obtain ⟨h, -⟩ := id C.spl
  have := congrArg (· ≫ pullback.snd C.p (gen O k)) (h δ)
  simpa only [Category.assoc, pullback.lift_snd] using this


variable (H) in
private abbrev sB (g : H.Γ) : pullback (H.s g ≫ H.q) (spf τ) ⟶ pullback H.q (spf τ) := bcMap (spf τ) (H.s g) rfl


variable (H) in
private abbrev tB (g : H.Γ) : pullback (H.s g ≫ H.q) (spf τ) ⟶ pullback H.q (spf τ) := bcMap (spf τ) (H.t g) (H.comm g)

private abbrev aB (δ : C.Δ) : pullback H.q (spf τ) ⟶ pullback H.q (spf τ) := bcMap (spf τ) (C.a δ) (a_q C δ)

private theorem a_spl : Splits (piK' τ φ C hφ) (piK' τ φ C hφ) (aB τ C) := by
  haveI := C.finπ
  haveI := C.etπ
  have h0 := splits_bc.1 (piK C) (piK C) C.Δ C.a (pullback.fst H.q (spf τ)) C.spl
  have hσ : ∀ δ, aB τ C δ ≫ piK' τ φ C hφ = piK' τ φ C hφ := by
    intro δ
    obtain ⟨ha, -⟩ := id C.spl
    have e1 : piK' τ φ C hφ ≫ wG τ φ C hφ = pullback.fst H.q (spf τ) ≫ piK C := (sqPi τ φ C hφ).w.symm
    apply (sqG τ φ C hφ).hom_ext
    · rw [Category.assoc, e1, ← Category.assoc, bcMap_fst, Category.assoc, ha δ]
    · rw [Category.assoc, piK'_snd, bcMap_snd]
  refine (splits_bc.2 _ _ _ _ (sqPi τ φ C hφ) (piK' τ φ C hφ) C.Δ (aB τ C) hσ).2 ?_
  have e1 : piK' τ φ C hφ ≫ wG τ φ C hφ = pullback.fst H.q (spf τ) ≫ piK C := (sqPi τ φ C hφ).w.symm
  have e2 : (fun δ => aB τ C δ ≫ pullback.fst H.q (spf τ)) = fun δ => pullback.fst H.q (spf τ) ≫ C.a δ :=
    funext fun δ => bcMap_fst _ _ _
  rw [e1, e2]
  exact h0

private def bcC : Cover (bcAlong H τ) θ O' where
  Y := pullback C.p (spf φ)
  p := pullback.snd C.p (spf φ)
  smooth := MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback C.p (spf φ)) C.smooth
  proj := GlobalTheory.ProjSpace.isProjOver_pullback_snd φ C.proj
  π := piY τ φ C hφ
  ov := piY_snd τ φ C hφ
  Δ := C.Δ
  grp := C.grp
  fin := C.fin
  a := aB τ C
  finπ := MorphismProperty.of_isPullback (P := @IsFinite) (sqPi τ φ C hφ) C.finπ
  etπ := MorphismProperty.of_isPullback (P := @Etale) (sqPi τ φ C hφ) C.etπ
  one := by
    apply pullback.hom_ext
    · erw [bcMap_fst, C.one, Category.comp_id]
    · erw [bcMap_snd, Category.id_comp]
  mul x y := by
    apply pullback.hom_ext
    · erw [bcMap_fst, Category.assoc, bcMap_fst, ← Category.assoc, bcMap_fst, Category.assoc, C.mul]
    · erw [bcMap_snd, Category.assoc, bcMap_snd, bcMap_snd]
  spl := a_spl τ φ C hφ
  fix δ := by
    obtain ⟨g, hi, ht, hθ⟩ := C.fix δ
    have sq : IsPullback (pullback.fst (H.s g ≫ H.q) (spf τ)) (sB τ H g) (H.s g) (pullback.fst H.q (spf τ)) :=
      sq_up rfl (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback H.q (spf τ)) (bcMap_fst _ _ _) (bcMap_snd _ _ _)
    refine ⟨g, sq.isIso_snd_of_isIso, ?_, hθ⟩
    change tB τ H g = sB τ H g ≫ aB τ C δ
    apply pullback.hom_ext
    · rw [bcMap_fst, Category.assoc, bcMap_fst, ← Category.assoc, bcMap_fst, Category.assoc, ht]
    · rw [bcMap_snd, Category.assoc, bcMap_snd, bcMap_snd]
  dim := by
    obtain ⟨d, hd⟩ := C.dim
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange d
    exact ⟨d, MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) (IsPullback.of_hasPullback C.p (spf φ)) hd⟩

private theorem bcC_onto (h : C.Onto) : (bcC τ φ C hφ).Onto :=
  MorphismProperty.of_isPullback (P := @Surjective) (sqPi τ φ C hφ) h

private theorem bcC_lies (g : H.Γ) {T : Scheme.{0}} (s t : T ⟶ C.Y) (m : ℕ) (hL : C.Lies g s t m) {T' : Scheme.{0}}
    (v : T' ⟶ T) (s' t' : T' ⟶ pullback C.p (spf φ)) (hv : IsPullback v s' s (pullback.fst C.p (spf φ)))
    (ht : t' ≫ pullback.fst C.p (spf φ) = v ≫ t) (hp : t' ≫ pullback.snd C.p (spf φ) = s' ≫ pullback.snd C.p (spf φ)) :
    (bcC τ φ C hφ).Lies g s' t' m := by
  obtain ⟨hm, κ, h, h2, hF⟩ := hL
  have hsf : sB τ H g ≫ pullback.fst H.q (spf τ) = pullback.fst (H.s g ≫ H.q) (spf τ) ≫ H.s g := bcMap_fst _ _ _
  have htf : tB τ H g ≫ pullback.fst H.q (spf τ) = pullback.fst (H.s g ≫ H.q) (spf τ) ≫ H.t g := bcMap_fst _ _ _
  have hss : sB τ H g ≫ pullback.snd H.q (spf τ) = pullback.snd (H.s g ≫ H.q) (spf τ) := bcMap_snd _ _ _
  have hts : tB τ H g ≫ pullback.snd H.q (spf τ) = pullback.snd (H.s g ≫ H.q) (spf τ) := bcMap_snd _ _ _
  have l1 : (pullback.fst (H.s g ≫ H.q) (spf τ) ≫ κ) ≫ s = (sB τ H g ≫ piY τ φ C hφ) ≫ pullback.fst C.p (spf φ) := by
    rw [Category.assoc, Category.assoc, piY_fst, ← Category.assoc (sB τ H g), hsf, Category.assoc, h]
  have k1 : hv.lift _ _ l1 ≫ v = pullback.fst (H.s g ≫ H.q) (spf τ) ≫ κ := hv.lift_fst _ _ _
  have k2 : hv.lift _ _ l1 ≫ s' = sB τ H g ≫ piY τ φ C hφ := hv.lift_snd _ _ _
  generalize hv.lift _ _ l1 = κ' at k1 k2
  have e1 : κ' ≫ t' = tB τ H g ≫ piY τ φ C hφ := by
    apply pullback.hom_ext
    · rw [Category.assoc, ht, ← Category.assoc, k1, Category.assoc, Category.assoc, piY_fst, h2, ← Category.assoc (tB τ H g), htf,
        Category.assoc]
    · rw [Category.assoc, hp, ← Category.assoc, k2, Category.assoc, Category.assoc, piY_snd, ← Category.assoc, ← Category.assoc, hss, hts]

  let b : pullback (piY τ φ C hφ) s' ⟶ pullback C.π s :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst H.q (spf τ)) (pullback.snd _ _ ≫ v) (by
      rw [Category.assoc, ← piY_fst τ φ C hφ, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, hv.w])
  have b1 : b ≫ pullback.fst C.π s = pullback.fst (piY τ φ C hφ) s' ≫ pullback.fst H.q (spf τ) := pullback.lift_fst _ _ _
  have b2 : b ≫ pullback.snd C.π s = pullback.snd (piY τ φ C hφ) s' ≫ v := pullback.lift_snd _ _ _
  have sA : IsPullback (pullback.fst (piY τ φ C hφ) s') (b ≫ pullback.snd C.π s) (pullback.fst H.q (spf τ) ≫ C.π) s := by
    rw [b2, ← piY_fst τ φ C hφ]
    exact (IsPullback.of_hasPullback (piY τ φ C hφ) s').paste_vert hv.flip
  have sB' : IsPullback (pullback.fst (piY τ φ C hφ) s') b (pullback.fst H.q (spf τ)) (pullback.fst C.π s) :=
    IsPullback.of_bot sA b1.symm (IsPullback.of_hasPullback C.π s)
  have sC : IsPullback b (pullback.fst (piY τ φ C hφ) s' ≫ pullback.snd H.q (spf τ)) (pullback.fst C.π s ≫ H.q) (spf τ) :=
    sB'.flip.paste_vert (IsPullback.of_hasPullback H.q (spf τ))
  have h' : sB τ H g ≫ piY τ φ C hφ = κ' ≫ s' := k2.symm
  have sq : IsPullback (pullback.fst (H.s g ≫ H.q) (spf τ)) (pullback.lift (sB τ H g) κ' h') (pullback.lift (H.s g) κ h) b := by
    refine sq_up (by rw [pullback.lift_fst_assoc]) (IsPullback.of_hasPullback _ _) sC ?_ ?_
    · apply pullback.hom_ext
      · rw [Category.assoc, b1, ← Category.assoc, pullback.lift_fst, hsf, Category.assoc, pullback.lift_fst]
      · rw [Category.assoc, b2, ← Category.assoc, pullback.lift_snd, k1, Category.assoc, pullback.lift_snd]
    · rw [← Category.assoc, pullback.lift_fst, hss]
  exact ⟨hm, κ', h', e1, fEt_bc.1 _ _ _ _ m sq hF⟩

private theorem bcC_good (h : C.Good) : (bcC τ φ C hφ).Good := by
  intro g
  obtain ⟨T, s, t, d, m, hs, hst, hL⟩ := h g
  have hv := IsPullback.of_hasPullback s (pullback.fst C.p (spf φ))
  have c : (pullback.fst s (pullback.fst C.p (spf φ)) ≫ t) ≫ C.p =
      (pullback.snd s (pullback.fst C.p (spf φ)) ≫ pullback.snd C.p (spf φ)) ≫ spf φ := by
    rw [Category.assoc, hst, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, pullback.condition]
  have sq := IsPullback.of_hasPullback C.p (spf φ)
  exact ⟨pullback s (pullback.fst C.p (spf φ)), pullback.snd _ _, sq.lift _ _ c, d, m, fEt_bc.1 _ _ _ _ d hv hs,
    sq.lift_snd _ _ _, bcC_lies τ φ C hφ g s t m hL _ _ _ hv (sq.lift_fst _ _ _) (sq.lift_snd _ _ _)⟩

end

theorem bcCover : BcCover := by
  intro k K O O' L _ _ _ _ _ _ _ τ φ hφ H θ C
  refine ⟨bcC τ φ C hφ, pullback.fst C.p (spf φ), IsPullback.of_hasPullback C.p (spf φ), piY_fst τ φ C hφ,
    bcC_onto τ φ C hφ, bcC_good τ φ C hφ, ?_⟩
  intro g T s t m _ hL T' v s' t' hv ht hp
  exact bcC_lies τ φ C hφ g s t m hL v s' t' hv ht hp

end UpperTheory.Gal.Seam

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.CrysStep
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain GlobalTheory.EtC TensorProduct
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst CrystallineSemistableComparison UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.Seam

private theorem mat_mul' {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (n : ℕ) {a : ℕ}
    (b : Module.Basis (Fin a) ℚ_[l] (M.V n)) (σ σ' : K.fixingSubgroup) :
    M.mat n b (σ * σ') = M.mat n b σ * M.mat n b σ' := by
  have h : M.act n (σ * σ') = M.act n σ * M.act n σ' := by
    simp only [Model.act, map_mul]
    rfl
  rw [Model.mat, h, LinearMap.toMatrix_mul]
  rfl

private theorem mat_one' {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (n : ℕ) {a : ℕ}
    (b : Module.Basis (Fin a) ℚ_[l] (M.V n)) : M.mat n b 1 = 1 := by
  have h : M.act n 1 = 1 := by
    simp only [Model.act, map_one]
    rfl
  rw [Model.mat, h, LinearMap.toMatrix_one]

theorem UpperTheory.Gal.Seam.crysStep :
    CrystallineSemistableComparison.SmoothModelCrystalline → NiceBc → LocTower → BcCover → IntMap → GoodOf → MatIn → SubAdm → GrCrys → UpperTheory.Gal.Int.Geo.CrysStep := by
  intro hCS hNB hLT hBC hIM hGO hMI hSA hGC E Ω _ _ _ _ _ l _ H θ hN dd ρ hc hp w hw C hOn P AI hT A hA O _ _ _ Bw hj
  obtain ⟨ρ₀, hM, hG⟩ := hp
  obtain ⟨φ, hφ, -⟩ := hIM E Ω l w A hA O Bw hj
  haveI := Bw.Kw.2
  have hN' := hNB E _ (kOf Bw) H hN
  obtain ⟨ρ₁, hM₁, hρ⟩ := hLT l E ↥Bw.Kw.1 Ω (PadicAlgCl l) (kOf Bw) Bw.j (fun _ => rfl) H hN (Om l) θ dd ρ₀ hM
  obtain ⟨C', u, -, -, hOn', -, -⟩ := hBC E ↥Bw.Kw.1 (Ow w) ↥(OK l Bw.Kw.1) (Om l) (kOf Bw) φ hφ H θ C
  obtain ⟨N, a, b, M, hinj, hmat⟩ := hMI l Bw.Kw (bcAlong H (kOf Bw)) θ hN' C' (hOn' hOn) dd ρ₁ hM₁
  obtain ⟨FreeQuotientRank⟩ := UpperTheory.Lit.Cmp.locTied6 l P AI hT
  have hgood : (mod C').Good := hGO l Bw.Kw.1 (mod C') C'.smooth C'.proj
  have hcr : IsCrysAt P Bw (ρ₀.comp (Dec (F := E) A).subtype) := by
    refine hSA l P AI hT E Ω (Dec (F := E) A) O Bw N dd a (fun n => (mod C').mat n (b n)) _ (fun n => ⟨mat_one' _ _ _, mat_mul' _ _ _, ?_⟩) M hinj ?_
    · exact isAdmP_of_isAdm FreeQuotientRank (hCS l Bw.Kw.1 (mod C') hgood C'.smooth n (a n) (b n))
    · intro g
      have := hmat (Bw.e g)
      rw [this]
      congr 2
      exact hρ _ _ fun x => Bw.e_comm g x
  obtain ⟨c, hc'⟩ := hG
  exact hGC l P AI hT E Ω _ O Bw dd _ _ ⟨c, fun g => hc' g⟩ hcr
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.GoodOf
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry CrystallineSemistableComparison

namespace UpperTheory.Gal.Seam

section Ring

variable (O : Type) [CommRing O] (ϖ : O) (n : ℕ)

private abbrev chartI : Ideal (MvPolynomial (Fin (n + 1)) O) :=
  Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1), MvPolynomial.X i) - MvPolynomial.C ϖ}

private theorem prod_one_branch :
    (∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1), (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) O)) =
      MvPolynomial.X 0 := by
  have hs : Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      ext
      simp only [Fin.val_zero]
      omega
    · rintro rfl
      simp
  rw [hs, Finset.prod_singleton]

private def evalFirst : MvPolynomial (Fin (n + 1)) O →+* MvPolynomial (Fin n) O :=
  (MvPolynomial.aeval (Fin.cons (MvPolynomial.C ϖ) MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin n) O)).toRingHom

private def toPoly : (MvPolynomial (Fin (n + 1)) O ⧸ chartI O ϖ n) →+* MvPolynomial (Fin n) O :=
  Ideal.Quotient.lift _ (evalFirst O ϖ n) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [prod_one_branch]
    simp [evalFirst])

private def fromPoly : MvPolynomial (Fin n) O →+* (MvPolynomial (Fin (n + 1)) O ⧸ chartI O ϖ n) :=
  (Ideal.Quotient.mk _).comp (MvPolynomial.rename Fin.succ : MvPolynomial (Fin n) O →ₐ[O] _).toRingHom

private theorem mk_X_zero :
    Ideal.Quotient.mk (chartI O ϖ n) (MvPolynomial.X 0) = Ideal.Quotient.mk (chartI O ϖ n) (MvPolynomial.C ϖ) := by
  rw [Ideal.Quotient.eq]
  apply Ideal.subset_span
  rw [prod_one_branch]
  rfl

private def chartEquiv : (MvPolynomial (Fin (n + 1)) O ⧸ chartI O ϖ n) ≃+* MvPolynomial (Fin n) O :=
  RingEquiv.ofRingHom (toPoly O ϖ n) (fromPoly O ϖ n)
    (by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · simp [toPoly, fromPoly, evalFirst]
      · simp [toPoly, fromPoly, evalFirst])
    (by
      refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
      · simp [toPoly, fromPoly, evalFirst]
      · refine Fin.cases ?_ (fun j => ?_) i
        · simp [toPoly, fromPoly, evalFirst, mk_X_zero]
        · simp [toPoly, fromPoly, evalFirst])

private theorem chartEquiv_algebraMap (o : O) :
    chartEquiv O ϖ n (algebraMap O _ o) = MvPolynomial.C o := by
  change toPoly O ϖ n (Ideal.Quotient.mk _ (MvPolynomial.C o)) = _
  simp [toPoly, evalFirst]

end Ring

theorem goodOf : GoodOf := by
  intro l _ K _ M hs hp
  refine ⟨hp, ?_⟩
  haveI : IsDiscreteValuationRing (OK l K) := OK_dvr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (OK l K)
  refine ⟨ϖ, hϖ, fun x => ?_⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    M.X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let e := (Scheme.ΓSpecIso (CommRingCat.of (OK l K))).commRingCatIsoToRingEquiv
  have hsm : (M.p.appLE ⊤ V le_top).hom.Smooth :=
    M.p.smooth_appLE (isAffineOpen_top _) hV le_top
  let φ : OK l K →+* Γ(M.X, V) := (M.p.appLE ⊤ V le_top).hom.comp e.symm.toRingHom
  have hφ : φ.Smooth := RingHom.Smooth.propertyIsLocal.respectsIso.2 _ _ hsm
  algebraize [φ]
  obtain ⟨r, hrx, hr⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth (OK l K)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hxr : x ∈ M.X.basicOpen r := by
    have h1 : hV.primeIdealOf ⟨x, hxV⟩ ∈ hV.fromSpec ⁻¹ᵁ M.X.basicOpen r := by
      rw [hV.fromSpec_preimage_basicOpen]
      exact hrx
    have h2 : hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) ∈ M.X.basicOpen r := h1
    rwa [hV.fromSpec_primeIdealOf] at h2
  have hstd : ((Scheme.ΓSpecIso (CommRingCat.of (OK l K))).inv ≫
      M.p.appLE ⊤ (M.X.basicOpen r) le_top).hom.IsStandardSmooth := by
    have := hV.isLocalization_basicOpen r
    rw [← RingHom.isStandardSmooth_algebraMap] at hr
    convert RingHom.isStandardSmooth_respectsIso.1 _
      (IsLocalization.algEquiv (.powers r) _ Γ(M.X, M.X.basicOpen r)).toRingEquiv hr
    ext a
    dsimp
    simp only [IsScalarTower.algebraMap_apply (OK l K) Γ(M.X, V) (Localization _),
      IsLocalization.map_eq]
    simp only [RingHom.algebraMap_toAlgebra, RingHomCompTriple.comp_apply,
      ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]
    rw [AlgEquiv.commutes]
    first
      | (rw [CommRingCat.comp_apply, ← Scheme.Hom.appLE_map (V := V) M.p le_top
            (homOfLE (M.X.basicOpen_le r)).op, CommRingCat.comp_apply]; rfl)
      | (simp only [φ, e, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
            Iso.commRingCatIsoToRingEquiv_symm_apply, ← CommRingCat.comp_apply,
            ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]; rfl)
  obtain ⟨k, g, hgC, hg⟩ := hstd.exists_etale_mvPolynomial
  refine ⟨M.X.basicOpen r, hV.basicOpen r, hxr, k + 1, 1, le_rfl, by omega,
    g.comp (chartEquiv (OK l K) ϖ k).toRingHom, ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (chartEquiv (OK l K) ϖ k).bijective) hg
  · rw [← hgC]
    ext a
    change g (chartEquiv (OK l K) ϖ k (algebraMap (OK l K) _ a)) = g (MvPolynomial.C a)
    congr 1
    exact chartEquiv_algebraMap (OK l K) ϖ k a

end UpperTheory.Gal.Seam
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.HopExS
section
open UpperTheory.Gal.Seam

private theorem bcSplits : UpperTheory.Gal.G3.BcSplits :=
  UpperTheory.Gal.G3.pBcSplits (UpperTheory.Gal.G3.pSplitsBasic (UpperTheory.Gal.G3.pSplitsPts UpperTheory.Gal.G3.pIsoPts) UpperTheory.Gal.G3.pPtsOfSplits)

private theorem hopSpec : UpperTheory.Gal.G3.HopSpec :=
  UpperTheory.Gal.G3.pHopSpec
    (UpperTheory.Gal.G3.pEtGood (UpperTheory.Gal.G3.pEtnGood (UpperTheory.Gal.G3.pFEtBasic UpperTheory.Gal.G3.pPtsOfSplits) UpperTheory.Gal.G3.pEtTr))
    (UpperTheory.Gal.G3.pBcGood bcSplits (UpperTheory.Gal.G3.pBcGal bcSplits))
    (UpperTheory.Gal.G3.pGalClos (UpperTheory.Gal.G3.pGalClosD (UpperTheory.Gal.G3.pSplitsPts UpperTheory.Gal.G3.pIsoPts)
      (UpperTheory.Gal.G3.pOrdEx UpperTheory.Gal.G3.pOrdStep)))
    (UpperTheory.Gal.G3.pOpEx UpperTheory.Gal.G3.pOpTr) UpperTheory.Gal.G3.pOpTr UpperTheory.Gal.G3.pOpEt
    (UpperTheory.Gal.G3.pOpBc bcSplits (UpperTheory.Gal.G3.pBcGal bcSplits)) bcSplits

theorem UpperTheory.Gal.Seam.hopExS :
    True → HopEx := by
  intro _ l _ k Ω _ _ _ _ _ H hN g
  obtain ⟨d, hd⟩ := hN.2.2 g
  have hl : (l : k) ≠ 0 := by
    intro h
    have h0 : (l : Ω) = 0 := by rw [← map_natCast (algebraMap k Ω), h, map_zero]
    exact (Fact.out : l.Prime).ne_zero (Nat.cast_eq_zero.mp h0)
  exact (hopSpec l hl H Ω g d hd).1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.NegVan
section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.Seam

private theorem H_subsingleton_of_neg (R : Type) [CommRing R] (E : Spc) (F : Shv R) {n : ℤ} (hn : n < 0) :
    Subsingleton (H R E F n) := by
  haveI hK : ((chains R).obj E).IsStrictlyLE 0 :=
    (inferInstance : CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0)
  haveI hL : (res R F).IsStrictlyGE 0 := by
    dsimp [res]
    infer_instance
  have hz : ∀ z : Cochain ((chains R).obj E) (res R F) n, z = 0 := by
    intro z
    apply Cochain.ext
    intro p q hpq
    by_cases hp : 0 < p
    · exact (CochainComplex.isZero_of_isStrictlyLE ((chains R).obj E) 0 p hp).eq_of_src _ _
    · exact (CochainComplex.isZero_of_isStrictlyGE (res R F) 0 q (by omega)).eq_of_tgt _ _
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective b
  congr 1
  apply Subtype.ext
  rw [hz x.1, hz y.1]

theorem UpperTheory.Gal.Seam.negVan :
    NegVan := by
  intro l _ X n hn
  haveI : ∀ k : ℕ, Subsingleton (HtL l k (sch.obj X) n 0) := fun k =>
    H_subsingleton_of_neg (ZMod (l ^ k)) (sch.obj X) (tw (l ^ k) 0) hn
  haveI : Subsingleton (Hl l (sch.obj X) n 0) := by
    dsimp only [Hl]
    infer_instance
  dsimp only [HQ]
  infer_instance
end

