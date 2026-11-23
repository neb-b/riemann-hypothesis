module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1340
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PQuotUniq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private lemma twisted_kernel_forms_nonvanishing (hE : EtDesc) (k : Type) [Field k] [IsAlgClosed k] (A A₁ A₂ : Over (Sp k)) [GrpObj A]
    [GrpObj A₁] [GrpObj A₂] (hA : IsAbelianScheme A) (hA₂ : IsAbelianScheme A₂)
    (ψ₁ : A ⟶ A₁) (ψ₂ : A ⟶ A₂) [IsMonHom ψ₁] [IsMonHom ψ₂] [IsFinite ψ₁.left] [Etale ψ₁.left] [Surjective ψ₁.left]
    (hker : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp k) (a : Over.mk t ⟶ A), a ≫ ψ₁ = 1 → a ≫ ψ₂ = 1) :
    ∃ θ : A₁ ⟶ A₂, ψ₁ ≫ θ = ψ₂ := by
  haveI := hA.smooth
  haveI := hA₂.proper
  haveI : AlgebraicGeometry.IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  have hw : ψ₂.left ≫ A₂.hom = ψ₁.left ≫ A₁.hom := by rw [Over.w, Over.w]
  obtain ⟨hepi, g, hg⟩ := hE ψ₁.left A₁.hom A₂.hom ψ₂.left hw (by
    intro Ω _ _ x y hxy
    have hxy' : x ≫ A.hom = y ≫ A.hom := by
      rw [← Over.w ψ₁, ← Category.assoc, hxy, Category.assoc]
    let X : Over.mk (x ≫ A.hom) ⟶ A := Over.homMk x
    let Y : Over.mk (x ≫ A.hom) ⟶ A := Over.homMk y hxy'.symm
    have h1 : X ≫ ψ₁ = Y ≫ ψ₁ := Over.OverMorphism.ext hxy
    have h2 : (X * Y⁻¹) ≫ ψ₁ = 1 := by
      have e := (IsMonHom.monoidHom ψ₁ (Over.mk (x ≫ A.hom))).map_mul X Y⁻¹
      have e' := map_inv (IsMonHom.monoidHom ψ₁ (Over.mk (x ≫ A.hom))) Y
      simp only [IsMonHom.monoidHom_apply] at e e'
      rw [e, e', h1, mul_inv_cancel]
    have h3 := hker Ω (x ≫ A.hom) (X * Y⁻¹) h2
    have e := (IsMonHom.monoidHom ψ₂ (Over.mk (x ≫ A.hom))).map_mul X Y⁻¹
    have e' := map_inv (IsMonHom.monoidHom ψ₂ (Over.mk (x ≫ A.hom))) Y
    simp only [IsMonHom.monoidHom_apply] at e e'
    rw [e, e', mul_inv_eq_one] at h3
    exact congrArg CommaMorphism.left h3)
  haveI := hepi
  refine ⟨Over.homMk g ?_, ?_⟩
  · rw [← cancel_epi ψ₁.left, ← Category.assoc, hg, hw]
  · exact Over.OverMorphism.ext hg

theorem UpperTheory.Gal.G3.pQuotUniq :
    EtDesc → QuotUniq := by
  intro hE k _ _ A A₁ A₂ _ _ _ _ _ _ hA hA₁ hA₂ ψ₁ ψ₂ h₁ h₂ f₁ e₁ s₁ f₂ e₂ s₂ hker
  obtain ⟨θ, hθ⟩ := twisted_kernel_forms_nonvanishing hE k A A₁ A₂ hA hA₂ ψ₁ ψ₂ (fun Ω _ _ t a => (hker Ω t a).1)
  obtain ⟨θ', hθ'⟩ := twisted_kernel_forms_nonvanishing hE k A A₂ A₁ hA hA₁ ψ₂ ψ₁ (fun Ω _ _ t a => (hker Ω t a).2)
  haveI : Flat ψ₁.left := inferInstance
  haveI : Flat ψ₂.left := inferInstance
  haveI : Epi ψ₁ := GlobalTheory.FlatQuotient.epi_of_flat_surjective ψ₁
  haveI : Epi ψ₂ := GlobalTheory.FlatQuotient.epi_of_flat_surjective ψ₂
  haveI : Epi (ψ₁ ⊗ₘ ψ₁) := GlobalTheory.FlatQuotient.epi_tensorHom ψ₁ ψ₁
  have i1 : θ ≫ θ' = 𝟙 _ := by
    rw [← cancel_epi ψ₁, ← Category.assoc, hθ, hθ', Category.comp_id]
  have i2 : θ' ≫ θ = 𝟙 _ := by
    rw [← cancel_epi ψ₂, ← Category.assoc, hθ', hθ, Category.comp_id]
  refine ⟨θ, ⟨θ', i1, i2⟩, ⟨?_, ?_⟩, hθ⟩
  · rw [← IsMonHom.one_hom ψ₁, Category.assoc, hθ, IsMonHom.one_hom ψ₂]
  · have h1 : (ψ₁ ⊗ₘ ψ₁) ≫ (θ ⊗ₘ θ) = ψ₂ ⊗ₘ ψ₂ := by
      rw [tensorHom_comp_tensorHom, hθ]
    rw [← cancel_epi (ψ₁ ⊗ₘ ψ₁), ← Category.assoc, ← IsMonHom.mul_hom ψ₁, Category.assoc, hθ,
      IsMonHom.mul_hom ψ₂, ← Category.assoc, h1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PRigid
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt)
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor GlobalTheory.CechPic GlobalTheory.AmpleRigid
open scoped TensorProduct CategoryTheory.Obj
universe u

private theorem diag_fst {S : Scheme.{0}} (A : Over S) :
    (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 A.left := by
  rw [← Over.comp_left, lift_fst]
  rfl

private theorem diag_snd {S : Scheme.{0}} (A : Over S) :
    (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 A.left := by
  rw [← Over.comp_left, lift_snd]
  rfl

section

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N : ℕ} {S S' : Scheme.{0}}
  {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : GObj gb N s} {o' : GObj gb N s'} {f : S' ⟶ S}

private theorem tensor_left_hom_ext_of_fst_snd {S : Scheme.{0}} {X Y : Over S} {W : Scheme.{0}} {u v : W ⟶ (X ⊗ Y).left}
    (h₁ : u ≫ (fst X Y).left = v ≫ (fst X Y).left) (h₂ : u ≫ (snd X Y).left = v ≫ (snd X Y).left) : u = v := by
  have hw : u ≫ (X ⊗ Y).hom = v ≫ (X ⊗ Y).hom := by
    rw [← Over.w (fst X Y), ← Category.assoc, h₁, Category.assoc]
  let U : Over.mk (u ≫ (X ⊗ Y).hom) ⟶ X ⊗ Y := Over.homMk u
  let V : Over.mk (u ≫ (X ⊗ Y).hom) ⟶ X ⊗ Y := Over.homMk v hw.symm
  have hUV : U = V := by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.OverMorphism.ext (by simpa [U, V] using h₁)
    · exact Over.OverMorphism.ext (by simpa [U, V] using h₂)
  exact congrArg CommaMorphism.left hUV

private theorem map_diag (m : GObjMap o' o f) :
    (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ m.φ₂ = m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left := by
  apply tensor_left_hom_ext_of_fst_snd
  · have key : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (fst o'.A o'.A).left ≫ m.φ = m.φ := by
      rw [← Category.assoc, diag_fst, Category.id_comp]
    rw [Category.assoc, m.sq.1, key, Category.assoc, diag_fst, Category.comp_id]
  · have key : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (snd o'.A o'.A).left ≫ m.φ = m.φ := by
      rw [← Category.assoc, diag_snd, Category.id_comp]
    rw [Category.assoc, m.sq.2, key, Category.assoc, diag_snd, Category.comp_id]

private theorem pull_diag_cls (m : GObjMap o' o f) :
    pull m.φ (cls (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (pull_isLB o.isLB _)) =
      cls (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) (pull_isLB o'.isLB _) := by
  rw [cls_pull o.isLB, cls_pull o'.isLB, ← pull_comp, ← map_diag m, pull_comp,
    ← cls_pull o.isLB _ (pull_isLB o.isLB m.φ₂),
    (cls_eq_iff (pull_isLB o.isLB m.φ₂) o'.isLB).2 (LBIso.symm m.pol)]

private theorem eq_at_point (hN : 3 ≤ N) (m m' : GObjMap o' o f) {K : Type} [Field K] [IsAlgClosed K] (j : Sp K ⟶ S') :
    pullback.fst o'.A.hom j ≫ m.φ = pullback.fst o'.A.hom j ≫ m'.φ := by
  have hA' : IsAbelianScheme ((Over.pullback j).obj o'.A) := by
    haveI := o'.ab.comm
    haveI := o'.ab.smooth
    haveI := o'.ab.proper
    haveI := o'.ab.geomConnected
    constructor
    · infer_instance
    · dsimp; infer_instance
    · dsimp; infer_instance
    · dsimp; infer_instance
  have c := (isGrpPullback_pullback o'.A j).comp m.cart
  have c' := (isGrpPullback_pullback o'.A j).comp m'.cart
  refine GlobalTheory.SiegRigid.eq_of_field (pull_isLB o.isLB _) o.ample hA' c c' ?_ hN ?_ ?_
  · rw [pull_comp, pull_comp, pull_diag_cls m, pull_diag_cls m']
  · intro h0
    let ψ : ℚ →+* K := (Spec.preimage (R := CommRingCat.of R) (S := CommRingCat.of K) (j ≫ s')).hom.comp
      (algebraMap ℚ R)
    have e0 : ψ (N : ℚ) = ψ 0 := by rw [map_natCast, map_zero]; exact h0
    have e1 : (N : ℚ) = 0 := ψ.injective e0
    norm_cast at e1
    omega
  · intro Ω _ _ t x hx
    let β : R →+* Ω := (Spec.preimage (R := CommRingCat.of R) (S := CommRingCat.of Ω) ((t ≫ j) ≫ s')).hom
    have hβ : (t ≫ j) ≫ s' = spMap β := by
      simp only [spMap, β, CommRingCat.ofHom_hom, Spec.map_preimage]
    obtain ⟨I, hI⟩ := o'.geom Ω (t ≫ j) β hβ
    let x₁ := pushHom (isGrpPullback_pullback o'.A j) (Over.mk t) x
    have hx₁ : x₁ ^ N = 1 := by
      simp only [x₁]
      rw [← map_pow, hx, map_one]
    obtain ⟨y, hy⟩ := (I.onto N (by omega) x₁).1 hx₁
    have hl : x.left ≫ pullback.fst o'.A.hom j = x₁.left := rfl
    have key : ∀ mm : GObjMap o' o f, x.left ≫ pullback.fst o'.A.hom j ≫ mm.φ =
        (toUnit (Over.mk (t ≫ j))).left ≫ f ≫ (o.eta y).left := by
      intro mm
      rw [← Category.assoc, hl, ← hy, ← hI y, Over.comp_left, Category.assoc, mm.eta y]
    rw [key m, key m']

end

theorem UpperTheory.Gal.G3.pRigid :
    Rigid := by
  intro p _ D R _ _ gb S S' s s' f hf N o o' m m'
  have hN : 3 ≤ (N : ℕ) := N.2.1
  obtain ⟨σ, hσmon, hσ⟩ := GlobalTheory.SiegRigid.exists_aut m.cart m'.cart
  have hid : σ.hom = 𝟙 o'.A := by
    refine GlobalTheory.eq_id_of_forall_geometric_fibre GlobalTheory.laws_without_cohomology.1 o'.A o'.ab σ.hom
      (IsMonHom.one_hom σ.hom) ?_
    intro t
    let K := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫
      S'.fromSpecResidueField t
    refine ⟨Sp K, pullback o'.A.hom j, j, pullback.fst o'.A.hom j, pullback.snd o'.A.hom j,
      IsLocalRing.closedPoint K, ?_, IsPullback.of_hasPullback _ _, ?_⟩
    · exact Scheme.fromSpecResidueField_apply t _
    · apply m'.cart.1.hom_ext
      · rw [Category.assoc, hσ, eq_at_point hN m m' j]
      · rw [Category.assoc, Over.w]
  rw [← hσ, hid, Over.id_left, Category.id_comp]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSigmaFEt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem exists_sigma_point {W : Scheme.{0}} {I : Type} (K : Type) [Field K]
    (y : Spec (CommRingCat.of K) ⟶ ∐ fun _ : I => W) :
    ∃ (i : I) (y' : Spec (CommRingCat.of K) ⟶ W), y' ≫ Sigma.ι (fun _ : I => W) i = y := by
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨⟨i, w⟩, hw⟩ := (sigmaMk (fun _ : I => W)).surjective (y pt)
  rw [sigmaMk_mk] at hw
  refine ⟨i, IsOpenImmersion.lift (Sigma.ι (fun _ : I => W) i) y ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨q, rfl⟩
  rw [Subsingleton.elim q pt]
  exact ⟨w, hw⟩

private theorem card_sigma_fibre {Y Z : Scheme.{0}} (s : Y ⟶ Z) (I : Type) (K : Type) [Field K]
    (x : Spec (CommRingCat.of K) ⟶ Z) :
    Nat.card {y : Spec (CommRingCat.of K) ⟶ ∐ (fun _ : I => Y) // y ≫ (Sigma.desc fun _ : I => s) = x} =
      Nat.card I * Nat.card {y' : Spec (CommRingCat.of K) ⟶ Y // y' ≫ s = x} := by
  let F : I × {y' : Spec (CommRingCat.of K) ⟶ Y // y' ≫ s = x} →
      {y : Spec (CommRingCat.of K) ⟶ ∐ (fun _ : I => Y) // y ≫ (Sigma.desc fun _ : I => s) = x} :=
    fun q => ⟨q.2.1 ≫ Sigma.ι (fun _ : I => Y) q.1, by
      rw [Category.assoc, Sigma.ι_desc]
      exact q.2.2⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i, a, ha⟩ ⟨j, b, hb⟩ h
      have h' : a ≫ Sigma.ι (fun _ : I => Y) i = b ≫ Sigma.ι (fun _ : I => Y) j :=
        congrArg Subtype.val h
      by_cases hij : i = j
      · subst hij
        have hab : a = b := (cancel_mono _).mp h'
        subst hab
        rfl
      · exfalso
        have hE := isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : I => Y) ⟨h'⟩ hij
        obtain ⟨p⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of K)))
        exact hE.false p
    · rintro ⟨y, hy⟩
      obtain ⟨i, y', rfl⟩ := exists_sigma_point K y
      refine ⟨⟨i, y', ?_⟩, rfl⟩
      rw [Category.assoc, Sigma.ι_desc] at hy
      exact hy
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_prod]

theorem UpperTheory.Gal.G3.pSigmaFEt :
    SigmaFEt := by
  intro Y Z s d I _ hs
  obtain ⟨hfin, het, hcard⟩ := hs
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have hid : IsFinite (Sigma.desc fun _ : I => 𝟙 Y) := by
    have h1 := GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin Y n
    have h2 : IsFinite ((Sigma.reindex e (fun _ : Fin n => Y)).hom ≫
        Sigma.desc fun _ : Fin n => 𝟙 Y) := inferInstance
    have h3 : (Sigma.desc fun _ : I => 𝟙 Y) =
        (Sigma.reindex e (fun _ : Fin n => Y)).hom ≫ Sigma.desc fun _ : Fin n => 𝟙 Y := by
      refine Sigma.hom_ext (f := fun _ : I => Y) _ _ fun i => ?_
      rw [Sigma.ι_desc, ← Category.assoc]
      erw [Sigma.ι_reindex_hom (f := fun _ : Fin n => Y) e i]
      rw [Sigma.ι_desc]
    rw [h3]
    exact h2
  have hfac : (Sigma.desc fun _ : I => s) = (Sigma.desc fun _ : I => 𝟙 Y) ≫ s := by
    refine Sigma.hom_ext (f := fun _ : I => Y) _ _ fun i => ?_
    simp
  have hloc : IsZariskiLocalAtSource @Etale.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  refine ⟨?_, ?_, ?_⟩
  · rw [hfac]
    infer_instance
  · exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{0}) fun _ => het
  · intro K _ _ x
    rw [card_sigma_fibre, hcard]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSumFn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem isAdmissible_flagPair_of_unitriangular_left_automorphism {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {m j : X.ι} {k h : G}
    (hk : k ∈ X.K j) (hh : X.admitted m j h) : X.admitted m j (k * h) := by
  refine ⟨X.Δ.mul_mem (X.K_le j k hk) hh.1, fun u hu => ?_⟩
  have h3 := (X.K j).mul_mem ((X.K j).mul_mem hk (hh.2 u hu)) ((X.K j).inv_mem hk)
  have e : k * h * u * (k * h)⁻¹ = k * (h * u * h⁻¹) * k⁻¹ := by group
  rw [e]
  exact h3

private theorem pl_left {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {F : Type} [Field F] (T : Th.{u} B F)
    {m j : X.ι} {k h : G} (hk : k ∈ X.K j) (hh : X.admitted m j h) : X.pl T m j (k * h) = X.pl T m j h := by
  have a := isAdmissible_flagPair_of_unitriangular_left_automorphism X hk hh
  have e : X.tr m j (k * h) a.1 a.2 = X.tr m j h hh.1 hh.2 := by
    rw [← X.tr_mul m j j h k hh.1 hh.2 (X.K_le j k hk)
      (fun u hu => (X.K j).mul_mem ((X.K j).mul_mem hk hu) ((X.K j).inv_mem hk)) a.1 a.2,
      X.tr_self j k _ _ hk, Category.comp_id]
  unfold Tower.pl
  rw [dite_eq_left a, dite_eq_left hh]
  simp only [e]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransComp :
    MultBasic → RelComp → TateDiff → TateTwist → TransComp := by
  intro hMB hRC hTD hTT p _ D G L R _ _ gb S s N₁ N₂ N₃ o₁ o₂ o₃ ψ₁ ψ₂ h₁ h₂ hI hA t1 t2
  obtain ⟨m1, a1, ⟨ψ₁', d₁, m1', a1', e1, e1', cp1⟩, ⟨c₁, cc1, ⟨iso1⟩, hm1⟩, g1⟩ := t1
  obtain ⟨m2, a2, ⟨ψ₂', d₂, m2', a2', e2, e2', cp2⟩, ⟨c₂, cc2, ⟨iso2⟩, hm2⟩, g2⟩ := t2
  haveI := m1
  haveI := m2
  haveI := m1'
  haveI := m2'
  refine ⟨inferInstance, ?_, ⟨ψ₂' ≫ ψ₁', d₁ * d₂, inferInstance, ?_, ?_, ?_, Nat.Coprime.mul_left cp1 cp2⟩,
    ⟨c₂ * c₁, Nat.Coprime.mul_left cc2 cc1, ⟨?_⟩, ?_⟩, ?_⟩
  · intro c
    rw [← Category.assoc, a1 c, Category.assoc, a2 c, Category.assoc]
  · intro c
    rw [← Category.assoc, a2' c, Category.assoc, a1' c, Category.assoc]
  · rw [Category.assoc, ← Category.assoc ψ₂, e2, MonObj.pow_comp, Category.id_comp,
      MonObj.comp_pow, e1, pow_mul]
  · rw [Category.assoc, ← Category.assoc ψ₁', e1', MonObj.pow_comp, Category.id_comp,
      MonObj.comp_pow, e2', mul_comm, pow_mul]
  · have hlb : (Hecke.lbPow o₁.P (c₂ * c₁)).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hpl : (o₃.P.pull (Hecke.sq2 (ψ₁ ≫ ψ₂))).IsLB := pull_isLB o₃.isLB _
    have hl1 : (Hecke.lbPow o₁.P c₁).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hl2 : (Hecke.lbPow o₂.P c₂).IsLB := LB.isLB_linComb o₂.isLB _ _
    have k1 := (GlobalTheory.CechPic.cls_eq_iff hl1 (pull_isLB o₂.isLB (Hecke.sq2 ψ₁))).2 iso1
    have k2 := (GlobalTheory.CechPic.cls_eq_iff hl2 (pull_isLB o₃.isLB (Hecke.sq2 ψ₂))).2 iso2
    rw [Hecke.Comp.cls_lbPow' o₁.isLB, GlobalTheory.CechPic.cls_pull o₂.isLB] at k1
    rw [Hecke.Comp.cls_lbPow' o₂.isLB, GlobalTheory.CechPic.cls_pull o₃.isLB] at k2
    apply (GlobalTheory.CechPic.cls_eq_iff hlb hpl).1
    rw [Hecke.Comp.cls_lbPow' o₁.isLB, GlobalTheory.CechPic.cls_pull o₃.isLB, Hecke.Comp.grpSchemeSquareProductMap_comp,
      GlobalTheory.CechPic.pull_comp, ← k2, map_nsmul, ← k1, smul_smul]
  · exact (hMB p).2.1 _ _ _ _ hm2 hm1
  · intro k _ _ t β hts
    obtain ⟨I1', I1'', ind1', ind1'', rel1⟩ := g1 k t β hts
    obtain ⟨I2', I2'', ind2', ind2'', rel2⟩ := g2 k t β hts
    obtain ⟨u, hu, ru⟩ := hTD p D G L R gb S s N₂ o₂ k t I1'' I2' ind1'' ind2'
    have hint : ∀ {M : ℕ} {g : G.GAf}, g ∈ L.KN M → Integ L g := fun hg =>
      UpperTheory.Gal.Int.Geo.integ_of_mem (UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hg)
    have rA := (hRC p D G L R gb S s N₁ N₂ N₂ o₁ o₂ o₂ k t I1' I1'' I2' ψ₁ (𝟙 _) h₁ u
      inferInstance inferInstance (hint hu)).2 rel1 ru
    have rB := (hRC p D G L R gb S s N₁ N₂ N₃ o₁ o₂ o₃ k t I1' I2' I2'' (ψ₁ ≫ 𝟙 _) ψ₂ (u * h₁) h₂
      inferInstance inferInstance hI).2 rA rel2
    have hu' : (h₂ * u * h₂⁻¹)⁻¹ ∈ L.KN N₃ := inv_mem (hA u hu)
    obtain ⟨J, indJ, rJ⟩ := hTT p D G L R gb S s N₃ o₃ k t I2'' ind2'' _ hu'
    have rC := (hRC p D G L R gb S s N₁ N₃ N₃ o₁ o₃ o₃ k t I1' I2'' J ((ψ₁ ≫ 𝟙 _) ≫ ψ₂) (𝟙 _)
      (h₂ * (u * h₁)) _ inferInstance inferInstance (hint hu')).2 rB rJ
    have hg : (h₂ * u * h₂⁻¹)⁻¹ * (h₂ * (u * h₁)) = h₂ * h₁ := by group
    rw [hg] at rC
    simp only [Category.comp_id] at rC
    exact ⟨I1', J, ind1', indJ, rC⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransDesc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem epi_of_isGrpPullback_etale_surjective {S S' : Scheme} (c : S' ⟶ S) [Etale c] [Surjective c] (A : Over S)
    (A' : Over S') [GrpObj A] [GrpObj A'] (a : A'.left ⟶ A.left) (ha : IsGrpPullback A' A c a) : Epi a := by
  haveI : Etale a := MorphismProperty.of_isPullback (P := @Etale) ha.1.flip ‹Etale c›
  haveI : Surjective a := MorphismProperty.of_isPullback (P := @Surjective) ha.1.flip ‹Surjective c›
  exact AlgebraicGeometry.Flat.epi_of_flat_of_surjective a

private theorem comp_eq_comp_of_over_left_comm {S S' : Scheme} {A B : Over S} {A' B' : Over S'}
    (a : A'.left ⟶ A.left) (b : B'.left ⟶ B.left) [Epi a] (u : A ⟶ A) (v : B ⟶ B) (u' : A' ⟶ A')
    (v' : B' ⟶ B') (f : A ⟶ B) (f' : A' ⟶ B')
    (hf : Over.Hom.left f' ≫ b = a ≫ Over.Hom.left f)
    (hu : Over.Hom.left u' ≫ a = a ≫ Over.Hom.left u)
    (hv : Over.Hom.left v' ≫ b = b ≫ Over.Hom.left v) (h' : u' ≫ f' = f' ≫ v') : u ≫ f = f ≫ v := by
  apply Over.OverMorphism.ext
  rw [← cancel_epi a]
  have e3 : Over.Hom.left u' ≫ Over.Hom.left f' = Over.Hom.left f' ≫ Over.Hom.left v' := by
    rw [← Over.comp_left, h', Over.comp_left]
  simp only [Over.comp_left]
  calc a ≫ Over.Hom.left u ≫ Over.Hom.left f
        = Over.Hom.left u' ≫ Over.Hom.left f' ≫ b := by rw [← reassoc_of% hu, ← hf]
    _ = Over.Hom.left f' ≫ Over.Hom.left v' ≫ b := by rw [reassoc_of% e3]
    _ = a ≫ Over.Hom.left f ≫ Over.Hom.left v := by rw [hv, reassoc_of% hf]

theorem UpperTheory.Gal.G3.pTransDesc :
    IsogFEt → TatePull → HomDesc → PolDesc → TransDesc := by
  intro hIsog hTate hHom hPol p _ D G L R _ _ gb S S' _ s s' c _ _ _ hcs N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ ψ' h hsq hT
  obtain ⟨hmon', hact', ⟨χ', d, hχmon', hχact', hd1', hd2', hdp⟩, ⟨e, hep, hpol', hint⟩, hgeo'⟩ := hT
  haveI : Epi m₁.φ := epi_of_isGrpPullback_etale_surjective c o₁.A o₁'.A m₁.φ m₁.cart
  haveI : Epi m₂.φ := epi_of_isGrpPullback_etale_surjective c o₂.A o₂'.A m₂.φ m₂.cart
  have hH := hHom S S' c o₁.A o₂.A o₁'.A o₂'.A o₁.ab o₂.ab o₂'.ab m₁.φ m₂.φ m₁.cart m₂.cart ψ ψ' hsq hmon'
  have hmon : IsMonHom ψ := hH.1
  have hdpos : 0 < d := Nat.pos_of_ne_zero (by
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' ((Nat.coprime_zero_left p).mp hdp))
  obtain ⟨hfin, -, hsurj⟩ := hIsog R S' s' o₁'.A o₂'.A o₁'.ab o₂'.ab ψ' χ' d hdpos hmon' hχmon' hd1' hd2'
  obtain ⟨χ, hχsq, hd1, hd2⟩ := hH.2 χ' d hχmon' hsurj hfin hd1' hd2'
  have hχmon : IsMonHom χ := (hHom S S' c o₂.A o₁.A o₂'.A o₁'.A o₂.ab o₁.ab o₁'.ab m₂.φ m₁.φ
    m₂.cart m₁.cart χ χ' hχsq hχmon').1
  refine ⟨hmon, fun b => comp_eq_comp_of_over_left_comm m₁.φ m₂.φ _ _ _ _ ψ ψ' hsq (m₁.act b) (m₂.act b) (hact' b),
    ⟨χ, d, hχmon, fun b => comp_eq_comp_of_over_left_comm m₂.φ m₁.φ _ _ _ _ χ χ' hχsq (m₂.act b) (m₁.act b) (hχact' b),
      hd1, hd2, hdp⟩,
    ⟨e, hep, hPol D.toG R gb S S' s s' c N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ ψ' hmon hsq e hpol', hint⟩, ?_⟩
  intro k _ _ t β htβ
  obtain ⟨v, hv⟩ := ‹Surjective c›.surj (UpperTheory.Gal.TranscendenceTraces.pt t)
  obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds c k t v hv
  subst hz
  have hz' : z ≫ s' = spMap β := by
    rw [← hcs, ← Category.assoc]
    exact htβ
  obtain ⟨I₁', I₂', hI₁', hI₂', hiff'⟩ := hgeo' k z β hz'
  obtain ⟨-, hT1⟩ := hTate p D R gb S S' s s' c N₁ o₁ o₁' m₁ k z
  obtain ⟨-, hT2⟩ := hTate p D R gb S S' s s' c N₂ o₂ o₂' m₂ k z
  obtain ⟨I₁, hInd₁, hev₁⟩ := hT1 I₁'
  obtain ⟨I₂, hInd₂, hev₂⟩ := hT2 I₂'
  refine ⟨I₁, I₂, hInd₁ hI₁', hInd₂ hI₂', fun n hn hnp x y => ?_⟩
  have e1 : Over.Hom.left (I₁'.ev n x) ≫ m₁.φ = Over.Hom.left (I₁.ev n x) := hev₁ n x
  have e2 : Over.Hom.left (I₂'.ev n y) ≫ m₂.φ = Over.Hom.left (I₂.ev n y) := hev₂ n y
  rw [← hiff' n hn hnp x y]
  constructor
  · intro hxy
    apply Over.OverMorphism.ext
    apply m₂.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hsq, ← Category.assoc, e1, ← Over.comp_left, hxy, e2]
    · rw [Over.w, Over.w]
  · intro hxy
    apply Over.OverMorphism.ext
    rw [Over.comp_left, ← e1, ← e2, Category.assoc, ← hsq, ← Category.assoc, ← Over.comp_left, hxy]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransFree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransFree :
    KNCong → TransFree := by
  intro hK p _ D G L R _ _ gb k _ _ s N o u hu hT
  obtain ⟨-, -, -, -, hp⟩ := hT
  obtain ⟨I', I'', h', h'', hr⟩ := hp k (𝟙 _) (Spec.preimage (𝟙 _ ≫ s)).hom (by
    simp [spMap])
  refine hK p D G L N.1 (by have := N.2.1; omega) N.2.2 u hu fun x => ?_
  exact (hr N.1 (by have := N.2.1; omega) N.2.2 x x).1 (by
    rw [← h' x, ← h'' x]; simp)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitCart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitCart :
    TransIso → WitCart := by
  intro hI p _ D G L R _ _ gb N' N X' X u hu π Φ hW
  obtain ⟨-, o, ψ, φ, hT, rfl⟩ := hW
  have hψ : IsIso ψ := hI p D G L R gb X'.X X'.s N' N X'.univ o ψ u hu hT
  have hl : IsIso ψ.left := inferInstanceAs (IsIso ((Over.forget _).map ψ))
  have h₁ : IsPullback ψ.left X'.univ.A.hom o.A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩
  have h₂ := h₁.paste_horiz φ.cart.1
  rwa [Category.id_comp] at h₂
end

