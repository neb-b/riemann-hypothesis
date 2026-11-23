module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRetract
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafComplexMappingConeAcyclicOfQuasiIso
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem mappingCone_acyclic_of_quasiIso {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {K L : CochainComplex 𝒜 ℤ} (u : K ⟶ L) [QuasiIso u] :
    (CochainComplex.mappingCone u).Acyclic := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  have hu : HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map u) := by
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (inferInstance : QuasiIso u)
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at hu
  exact ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished u)).1 hu

theorem EtC.mappingCone_acyclic :
    ∀ (R : Type) [CommRing R] {C J : Cx R} (u : C ⟶ J) [QuasiIso u], (mappingCone u).Acyclic :=
  fun _ _ _ _ u _ => mappingCone_acyclic_of_quasiIso u

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sec_ext_glue : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg := by
  intro R _ F U
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).2
  refine ⟨fun a b ⟨S, hS, h⟩ => ?_, fun S hS s hs => ?_⟩
  · exact (hF S hS).isSeparatedFor.ext fun V g hg => h V g hg
  · let x : Presieve.FamilyOfElements (F.obj ⋙ forget _) S.arrows := fun V g hg => s V g hg
    have hx : x.Compatible := by
      rw [Presieve.compatible_iff_sieveCompatible]
      intro V W g k hg
      exact (hs V W g k hg).symm
    obtain ⟨a, ha, -⟩ := hF S hS x hx
    exact ⟨a, fun V g hg => ha g hg⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsGlueOfLocallyUnique
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.SecGlueLoc

theorem isSheaf_forget {R : Type} [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property)

theorem res_comp {R : Type} [CommRing R] (F : Shv R) {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res h (Sec.res g x) = Sec.res (h ≫ g) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem ext_of_sieve {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (S : Sieve U)
    (hS : S ∈ Scheme.etaleTopology U) (s t : Sec F U)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec.res g s = Sec.res g t) : s = t :=
  ((isSheaf_forget F) S hS).isSeparatedFor.ext (fun V g hg => h V g hg)

theorem exists_loc {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0})
    (A : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U → Prop)
    (h1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), A U x s → A V (g ≫ x) (Sec.res g s))
    (h2 : ∀ (U : Scheme.{0}) (x : U ⟶ X) (s t : Sec F U), A U x s → A U x t → s = t)
    (U : Scheme.{0}) (x : U ⟶ X) (h3 : Loc U fun V g => ∃ s, A V (g ≫ x) s) :
    ∃ s : Sec F U, Loc U fun V g => A V (g ≫ x) (Sec.res g s) := by
  obtain ⟨S, hS, hP⟩ := h3
  let t : Presieve.FamilyOfElements (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) S.arrows :=
    fun V g hg => (hP V g hg).choose
  have ht : ∀ (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g), A V (g ≫ x) (t g hg) :=
    fun V g hg => (hP V g hg).choose_spec
  have hc : t.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ w
    change Sec.res g₁ (t f₁ hf₁) = Sec.res g₂ (t f₂ hf₂)
    have a1 := h1 _ _ g₁ _ _ (ht _ f₁ hf₁)
    have a2 := h1 _ _ g₂ _ _ (ht _ f₂ hf₂)
    rw [← Category.assoc, w] at a1
    rw [← Category.assoc] at a2
    exact h2 _ _ _ _ a1 a2
  obtain ⟨s, hs, -⟩ := (isSheaf_forget F) S hS t hc
  refine ⟨s, S, hS, fun V g hg => ?_⟩
  have e : Sec.res g s = t g hg := hs g hg
  show A V (g ≫ x) (Sec.res g s)
  rw [e]
  exact ht V g hg

theorem loc_unique {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0})
    (A : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U → Prop)
    (h2 : ∀ (U : Scheme.{0}) (x : U ⟶ X) (s t : Sec F U), A U x s → A U x t → s = t)
    (U : Scheme.{0}) (x : U ⟶ X) (s t : Sec F U)
    (hs : Loc U fun V g => A V (g ≫ x) (Sec.res g s)) (ht : Loc U fun V g => A V (g ≫ x) (Sec.res g t)) :
    s = t := by
  obtain ⟨S, hS, hPs⟩ := hs
  obtain ⟨T, hT, hPt⟩ := ht
  refine ext_of_sieve F (S ⊓ T) (Scheme.etaleTopology.intersection_covering hS hT) s t (fun V g hg => ?_)
  exact h2 V (g ≫ x) _ _ (hPs V g hg.1) (hPt V g hg.2)

end GlobalTheory.EtC.SecGlueLoc


open GlobalTheory.EtC.SecGlueLoc in
theorem GlobalTheory.EtC.secGlue_of_loc : ∀ {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0}) (A : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U → Prop),
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), A U x s → A V (g ≫ x) (Sec.res g s)) →
    (∀ (U : Scheme.{0}) (x : U ⟶ X) (s t : Sec F U), A U x s → A U x t → s = t) →
    (∀ (U : Scheme.{0}) (x : U ⟶ X), Loc U fun V g => ∃ s, A V (g ≫ x) s) →
    ∃ e : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X), Sec.res g (e U x) = e V (g ≫ x)) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X) (s : Sec F U), A U x s → e U x = s := by
  intro R _ F X A h1 h2 h3
  let e : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U := fun U x => (exists_loc F X A h1 h2 U x (h3 U x)).choose
  have he : ∀ (U : Scheme.{0}) (x : U ⟶ X), Loc U fun V g => A V (g ≫ x) (Sec.res g (e U x)) :=
    fun U x => (exists_loc F X A h1 h2 U x (h3 U x)).choose_spec
  refine ⟨e, fun V U g x => ?_, fun U x s hs => ?_⟩
  · refine loc_unique F X A h2 V (g ≫ x) _ _ ?_ (he V (g ≫ x))
    obtain ⟨S, hS, hP⟩ := he U x
    refine ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W h hh => ?_⟩
    show A W (h ≫ g ≫ x) (Sec.res h (Sec.res g (e U x)))
    rw [res_comp, ← Category.assoc]
    exact hP W (h ≫ g) hh
  · refine loc_unique F X A h2 U x _ _ (he U x) ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h1 V U g x s hs⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsSepGlueOfSurjectiveFamily
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sec_sep_glue_of_points : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), (∀ i, Etale (j i)) → (∀ u : U, ∃ i v, j i v = u) → (∀ x : Sec F U, (∀ i, Sec.res (j i) x = 0) → x = 0) ∧ ∀ y : ∀ i, Sec F (V i), (∀ i k, Sec.res (pullback.fst (j i) (j k)) (y i) = Sec.res (pullback.snd (j i) (j k)) (y k)) → ∃ x : Sec F U, ∀ i, Sec.res (j i) x = y i := by
  intro R _ F U ι V j hE hS
  have hcov : Sieve.generate (Presieve.ofArrows V j) ∈ Scheme.etaleTopology U := by
    apply Precoverage.generate_mem_toGrothendieck
    refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun u => ?_, hE⟩
    obtain ⟨i, v, hv⟩ := hS u
    exact ⟨i, v, hv⟩
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 F.property
  have hfor := (Presieve.isSheafFor_iff_generate _).2 (hF _ hcov)
  rw [Presieve.isSheafFor_arrows_iff_pullbacks] at hfor
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · obtain ⟨t, -, ht⟩ := hfor (fun _ => 0) (fun i k => by
      change (F.obj.map (pullback.fst (j i) (j k)).op).hom 0 = (F.obj.map (pullback.snd (j i) (j k)).op).hom 0
      rw [map_zero, map_zero])
    have h0 : (0 : Sec F U) = t := ht 0 (fun i => by
      change (F.obj.map (j i).op).hom 0 = 0
      exact map_zero _)
    exact (ht x hx).trans h0.symm
  · obtain ⟨t, ht, -⟩ := hfor y hy
    exact ⟨t, ht⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceSimplicesOverSubComposite
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SubSub

theorem hom_ext_val' {a b : ℕ} (f g : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (h : ∀ v : Fin (a + 1), ((f.toOrderHom v : Fin (b + 1)) : ℕ) = (g.toOrderHom v : Fin (b + 1))) : f = g :=
  SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun v => Fin.ext (h v)))

theorem along_along' {E : Spc} {U : Scheme.{0}} {N p r : ℕ} (x : Sx E N U) (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N)
    (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p) : (x.along a).along b = x.along (b ≫ a) := by
  unfold Sx.along
  rw [op_comp, E.map_comp]
  rfl

theorem sub_eq_along {E : Spc} {U : Scheme.{0}} {N : ℕ} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    x.sub j l h = x.along (SimplexCategory.subinterval j l h) := rfl

theorem res_along {E : Spc} {U V : Scheme.{0}} {N p : ℕ} (x : Sx E N U) (g : V ⟶ U)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) : (x.res g).along a = (x.along a).res g := by
  unfold Sx.along Sx.res
  have h1 := congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)) ((E.map a.op).naturality g.op)) x
  simpa only [ConcreteCategory.comp_apply] using h1

theorem map_along {E E' : Spc} {U : Scheme.{0}} {N p : ℕ} (x : Sx E N U) (f : E ⟶ E')
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) : (x.map f).along a = (x.along a).map f := by
  unfold Sx.along Sx.map
  have := f.naturality a.op
  have h2 := congrArg (fun φ => φ.app (op U)) this
  simp only [NatTrans.comp_app] at h2
  exact (congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)) h2) x).symm

theorem main : ∀ {E : Spc} {U : Scheme.{0}} {N : ℕ} (x : Sx E N U), (∀ (j l j' l' : ℕ) (h : j + l ≤ N) (h' : j' + l' ≤ l), (x.sub j l h).sub j' l' h' = x.sub (j + j') l' (by omega)) ∧ x.sub 0 N (by omega) = x ∧ (∀ (j l : ℕ) (h : j + l ≤ N), (∀ {V : Scheme.{0}} (g : V ⟶ U), (x.res g).sub j l h = (x.sub j l h).res g) ∧ (∀ {E' : Spc} (f : E ⟶ E'), (x.map f).sub j l h = (x.sub j l h).map f) ∧ x.sub j l h = x.along (SimplexCategory.subinterval j l h)) ∧ ∀ {p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p), (x.along a).along b = x.along (b ≫ a) := by
  intro E U N x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j l j' l' h h'
    rw [sub_eq_along, sub_eq_along, sub_eq_along, along_along']
    congr 1
    exact hom_ext_val' _ _ fun v => by
      show ((v : ℕ) + j') + j = v + (j + j')
      omega
  · have : SimplexCategory.subinterval (n := N) 0 N (by omega) = 𝟙 _ :=
      hom_ext_val' _ _ fun v => by
        show (v : ℕ) + 0 = v
        omega
    rw [sub_eq_along, this]
    unfold Sx.along
    simp
  · intro j l h
    refine ⟨fun g => res_along x g _, fun f => map_along x f _, rfl⟩
  · intro p r a b
    exact along_along' x a b

end GlobalTheory.EtC.SubSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleTensorDiagonalComplementOverBasicOpen
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_mod_f_of_surj (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A)
    (hsurj : ∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f})
    (x : A' ⊗[A] A') :
    ∃ (c : A) (v : A' ⊗[A] A'), x = algebraMap A (A' ⊗[A] A') c + algebraMap A (A' ⊗[A] A') f * v := by
  set P : A' ⊗[A] A' → Prop := fun x => ∃ (c : A) (v : A' ⊗[A] A'),
    x = algebraMap A (A' ⊗[A] A') c + algebraMap A (A' ⊗[A] A') f * v with hP
  have hadd : ∀ x y, P x → P y → P (x + y) := by
    rintro x y ⟨c₁, v₁, rfl⟩ ⟨c₂, v₂, rfl⟩
    exact ⟨c₁ + c₂, v₁ + v₂, by rw [map_add (f := _)]; ring⟩
  have hmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y ⟨c₁, v₁, rfl⟩ ⟨c₂, v₂, rfl⟩
    refine ⟨c₁ * c₂, algebraMap A (A' ⊗[A] A') c₁ * v₂ + v₁ * algebraMap A (A' ⊗[A] A') c₂
      + algebraMap A (A' ⊗[A] A') f * v₁ * v₂, ?_⟩
    rw [map_mul]; ring
  have himg : ∀ (g : A' →ₐ[A] A' ⊗[A] A') (a' : A'), P (g a') := by
    intro g a'
    obtain ⟨a, ha⟩ := hsurj a'
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp ha
    refine ⟨a, g y, ?_⟩
    have : a' = algebraMap A A' a + y * algebraMap A A' f := by rw [hy]; ring
    rw [this, map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes]; ring
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a b =>
    have h : a ⊗ₜ[A] b = (Algebra.TensorProduct.includeLeft (S := A) a) *
        (Algebra.TensorProduct.includeRight b) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [h]
    exact hmul _ _ (himg _ _) (himg _ _)
  | add x y hx hy => exact hadd _ _ hx hy

theorem etale_diag_complement (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A) :
    (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) →
    (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) →
    ∃ e u : A' ⊗[A] A', (∀ a : A', (a ⊗ₜ[A] (1 : A') - (1 : A') ⊗ₜ[A] a) * e = 0) ∧
      algebraMap A (A' ⊗[A] A') f * u = 1 - e := by
  intro hsurj hinj
  obtain ⟨t, ht, ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := A')).1
    inferInstance
  obtain ⟨c, v, hcv⟩ := tensor_mod_f_of_surj A A' f hsurj (1 - t)
  have h0 : algebraMap A A' c + algebraMap A A' f * Algebra.TensorProduct.lmul' A v = 0 := by
    have := congrArg (Algebra.TensorProduct.lmul' A (S := A')) hcv
    rw [map_sub, map_one, ht1, sub_self, map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes] at this
    exact this.symm
  have hc : algebraMap A A' c ∈ Ideal.span {algebraMap A A' f} := by
    rw [Ideal.mem_span_singleton']
    exact ⟨-Algebra.TensorProduct.lmul' A v, by linear_combination -h0⟩
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp (hinj c hc)
  refine ⟨t, algebraMap A (A' ⊗[A] A') c' + v, ?_, ?_⟩
  · intro a
    rw [← neg_sub, neg_mul, ht a, neg_zero]
  · rw [hcv, ← hc', map_mul]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleSurjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem exists_affine_etale_surjective :
    ∀ (W : Scheme.{0}) [CompactSpace W], ∃ (V : Scheme.{0}) (f : V ⟶ W), IsAffine V ∧ Etale f ∧ Surjective f := by
  intro W _
  let 𝒰 := W.affineCover.finiteSubcover
  refine ⟨∐ 𝒰.X, Sigma.desc 𝒰.f, inferInstance, ?_, inferInstance⟩
  have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ ↦ inferInstance

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineHilbertChartBasicNeighbourhood
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem exists_basic_nhd : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (z : Z), ∃ (σ : Fin r ↪ Fin N) (U : Z.Opens), z ∈ U ∧ GlobalTheory.HilbAff.Basic A B e σ ((GlobalTheory.HilbAff.functor A B r).map U.ι.op y) := by
  intro A B _ _ _ N r e Z y z
  obtain ⟨W₀, hW₀, hzW₀, -⟩ := exists_isAffineOpen_mem_and_subset (show z ∈ (⊤ : Z.Opens) from trivial)
  let W : Z.affineOpens := ⟨W₀, hW₀⟩
  obtain ⟨hfin, hflat⟩ := GlobalTheory.T.affineHilbertSections_finite_flat A B r Z y W
  obtain ⟨σ, f, hf, hbij⟩ := GlobalTheory.T.exists_localizedModule_map_bijective_of_rankAtStalk_eq Γ(Z, W₀) (GlobalTheory.HilbAff.Sec A B y W) N r
    (fun j => GlobalTheory.HilbAff.gen A B y W (e j)) (GlobalTheory.T.affineHilbertSections_basis_span_eq_top A B N r e Z y W) (GlobalTheory.T.affineHilbertSections_rankAtStalk A B r Z y W)
    (hW₀.primeIdealOf ⟨z, hzW₀⟩)
  have hD := (GlobalTheory.T.affineHilbertCoordinateMap_basicOpen_bijective A B N r e σ Z y W f).2 hbij
  have hzf : z ∈ Z.basicOpen f := by
    have h1 : hW₀.primeIdealOf ⟨z, hzW₀⟩ ∈ hW₀.fromSpec ⁻¹ᵁ Z.basicOpen f := by
      rw [hW₀.fromSpec_preimage_basicOpen]; exact hf
    have h2 := hW₀.fromSpec_primeIdealOf ⟨z, hzW₀⟩
    have h3 : hW₀.fromSpec (hW₀.primeIdealOf ⟨z, hzW₀⟩) ∈ Z.basicOpen f := h1
    rw [h2] at h3
    exact h3
  refine ⟨σ, Z.basicOpen f, hzf, ?_⟩
  rw [GlobalTheory.HilbAff.basic_iff]
  intro W'
  apply GlobalTheory.T.affineHilbertCoordinateMap_restrict_bijective
  exact GlobalTheory.T.hilbertCoordinateMap_bijective_of_le_affine A B N r e σ Z y ⟨Z.basicOpen f, hW₀.basicOpen f⟩
    ⟨_, W'.2.image_of_isOpenImmersion (Z.basicOpen f).ι⟩ (Scheme.Opens.ι_image_le _ _) hD

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraMapEqOfFaithfullyFlatIncludeLeftEqI
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_algebraMap_eq_of_includeLeft_eq_includeRight :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B] (b : B),
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) b =
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) b →
      ∃ a : A, algebraMap A B a = b := by
  intro A B _ _ _ _ b hb
  have h := Algebra.IsEffective.of_faithfullyFlat A B
  have h0 : Algebra.TensorProduct.includeLeftSubRight A B b = 0 := by
    rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]
    simpa using hb
  obtain ⟨a, ha⟩ := (h b).mp h0
  exact ⟨a, by simpa using ha⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRetractStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseChange_retract_alt : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    IsLocalHom (algebraMap T O) → algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (ρ : Localization.AtPrime QA →+* A),
    QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
      (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective i₁ → IsLocalHom i₁ → i₁.comp j = i →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (γ₀ : EA →+* EA₁) (γ : Localization.AtPrime QA →+* Localization.AtPrime QA₁) (ρ' : EA₁ →+* A₁),
      QA₁.comap (algebraMap (Polynomial A₁) EA₁) = GlobalTheory.KeyOriginCut.originIdeal A₁ ∧
      jA₁.comp (algebraMap (Polynomial A₁) (Localization.AtPrime QA₁)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i₁) ∧
      jA₁.comp γ = jA ∧
      γ.comp (algebraMap EA (Localization.AtPrime QA)) = (algebraMap EA₁ (Localization.AtPrime QA₁)).comp γ₀ ∧
      γ.comp (algebraMap A (Localization.AtPrime QA)) = (algebraMap A₁ (Localization.AtPrime QA₁)).comp j ∧
      ρ'.comp γ₀ = j.comp (ρ.comp (algebraMap EA (Localization.AtPrime QA))) ∧
      ρ'.comp (algebraMap A₁ EA₁) = RingHom.id A₁ ∧
      ρ' (algebraMap (Polynomial A₁) EA₁ Polynomial.X) = 0 ∧
      (∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ (Localization.AtPrime QA₁) x) ∈
        Ideal.span {algebraMap (Polynomial T) O Polynomial.X}) ∧
      (∀ x : EA₁, ρ' x = 0 → ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}) := by
  first | (exact @GlobalTheory.KeyOriginBaseChangeCons.exists_baseChange_retract) | (exact GlobalTheory.KeyOriginBaseChangeCons.exists_baseChange_retract) | (intros; apply GlobalTheory.KeyOriginBaseChangeCons.exists_baseChange_retract <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNatural
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_cochain_ev_eq_of_natural :
    ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
      (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
      (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
        Sec.res g (a p s h U x) = a p s h V (x.res g)) →
      ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x := by
  intro R _ E I n a ha
  have components : ∀ (i j : ℤ) (hij : i + n = j), ∃ φ : ((chains R).obj E).X i ⟶ I.X j,
      ∀ (p : ℕ) (hp : i = -(p : ℤ)) U x,
        Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ)
          (freeGen R _ U x) = a p j (hp ▸ hij) U x := by
    intro i j hij
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := CupSpec.free_exists (R := R) _ _ (a k j hij) (ha k j hij)
      refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp U x => ?_⟩
      obtain rfl : k = p := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ U x
    · exact ⟨0, fun p hp => by omega⟩
  choose φ hφ using components
  refine ⟨Cochain.mk φ, fun p s h U x => ?_⟩
  have hEval := hφ _ _ h p rfl U x
  rw [eqToHom_refl, Category.id_comp] at hEval
  exact hEval

end GlobalTheory.EtC
end

