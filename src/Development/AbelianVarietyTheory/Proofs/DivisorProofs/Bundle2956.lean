module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0580
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2896
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantFieldConstCoeffs
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2938
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2941
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2935
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneIntegralityAndFaithful
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

namespace GlobalTheory.Dieu.Integrality

variable {p : ℕ} [Fact p.Prime] (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem map_id' (G : PDivGroup p k) : T.map (𝟙 G) = LinearMap.id :=
  (_root_.GlobalTheory.Dieu.base_functor_props p _ T.base k G G G trivial trivial trivial).1

theorem map_comp' {G H K : PDivGroup p k} (f : G ⟶ H) (g : H ⟶ K) :
    T.map (f ≫ g) = T.map f ∘ₗ T.map g :=
  (_root_.GlobalTheory.Dieu.base_functor_props p _ T.base k G H K trivial trivial trivial).2.1 f g

theorem map_pow_smul' {G H : PDivGroup p k} (n : ℕ) (f : G ⟶ H) (m : T.M H) :
    T.map ((p : ℤ_[p]) ^ n • f) m = p ^ n • T.map f m :=
  (_root_.GlobalTheory.Dieu.base_functor_props p _ T.base k G H H trivial trivial trivial).2.2.2.2.1 n f m

theorem red_map' {G H : PDivGroup p k} (f : G ⟶ H) (m : T.M H) :
    T.red G (T.map f m) = rigExtMap f (T.red H m) :=
  (_root_.GlobalTheory.Dieu.base_functor_props p _ T.base k G H H trivial trivial trivial).2.2.2.2.2.1 f m

theorem eq_zero_of_pow_smul' {G : PDivGroup p k} (n : ℕ) (m : T.M G) (h : p ^ n • m = 0) : m = 0 :=
  (_root_.GlobalTheory.Dieu.base_functor_props p _ T.base k G G G trivial trivial trivial).2.2.2.2.2.2.2.2 n m h

def DivP {G H : PDivGroup p k} (f : G ⟶ H) : Prop := ∀ m, ∃ m', T.map f m = p • m'

theorem divP_comp {G' G H H' : PDivGroup p k} (a : G' ⟶ G) (f : G ⟶ H) (b : H ⟶ H')
    (hf : DivP T f) : DivP T (a ≫ f ≫ b) := by
  intro m
  obtain ⟨m', hm'⟩ := hf (T.map b m)
  refine ⟨T.map a m', ?_⟩
  rw [map_comp', map_comp', LinearMap.comp_apply, LinearMap.comp_apply, hm', map_nsmul]

theorem divP_iff_red {G H : PDivGroup p k} (f : G ⟶ H) : DivP T f ↔ rigExtMap f = 0 := by
  constructor
  · intro hf
    refine LinearMap.ext fun x => ?_
    obtain ⟨m, rfl⟩ := T.base.red_surjective H trivial x
    obtain ⟨m', hm'⟩ := hf m
    have h := (T.base.red_eq_zero G trivial (T.map f m)).2 ⟨m', hm'⟩
    change rigExtMap f (T.red H m) = 0
    exact (red_map' T f m).symm.trans h
  · intro hf m
    have h : T.red G (T.map f m) = 0 := by
      have h' := congrArg (fun φ => φ (T.red H m)) hf
      exact (red_map' T f m).trans h'
    exact (T.base.red_eq_zero G trivial _).1 h

theorem exists_of_isConn {G H : PDivGroup p k} (hG : G.IsConn) (f : G ⟶ H) (hf : DivP T f) :
    ∃ g : G ⟶ H, f = (p : ℤ_[p]) • g := by
  have hq : IsIsog ((p : ℤ_[p]) ^ 1 • 𝟙 G) := ((_root_.GlobalTheory.Dieu.isog_basics p k G).1 1).1
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.Dieu.exists_comp_eq_of_range_map_le p T k G G H _ f hG hq (by
    rintro x ⟨m, rfl⟩
    obtain ⟨m', hm'⟩ := hf m
    refine ⟨m', ?_⟩
    rw [hm', map_pow_smul', map_id', LinearMap.id_apply, pow_one])
  refine ⟨g, ?_⟩
  rw [← hg, Linear.smul_comp, Category.id_comp, pow_one]

theorem exists_of_isEt {G H : PDivGroup p k} (hG : G.IsEt) (hH : H.IsEt) (f : G ⟶ H)
    (hf : DivP T f) : ∃ g : G ⟶ H, f = (p : ℤ_[p]) • g := by
  have h1 : rigExtMap (dualHom G H f) = 0 :=
    _root_.GlobalTheory.PDivGroup.rigExtMap_dualHom_eq_zero_of_isEt p k G H f hG hH ((divP_iff_red T f).1 hf)
  obtain ⟨g', hg'⟩ := exists_of_isConn T (PDivGroup.dual_isConn_of_isEt p k H hH) _
    ((divP_iff_red T _).2 h1)
  obtain ⟨g, rfl⟩ := (dualHom_bijective (G := G) (H := H)).2 g'
  refine ⟨g, (dualHom_bijective (G := G) (H := H)).1 ?_⟩
  rw [hg', map_smul]

theorem exists_of_divP {G H : PDivGroup p k} (f : G ⟶ H) (hf : DivP T f) :
    ∃ g : G ⟶ H, f = (p : ℤ_[p]) • g := by
  obtain ⟨G₀, G₁, i₀, q₀, i₁, q₁, hG₀, hG₁, -, -, hG⟩ :=
    PDivGroup.exists_isConn_isEt_splitting p k G
  obtain ⟨H₀, H₁, j₀, r₀, j₁, r₁, hH₀, hH₁, -, -, hH⟩ :=
    PDivGroup.exists_isConn_isEt_splitting p k H
  obtain ⟨g₀, hg₀⟩ := exists_of_isConn T hG₀ (i₀ ≫ f) (by
    simpa using divP_comp T i₀ f (𝟙 H) hf)
  obtain ⟨g₁, hg₁⟩ := exists_of_isEt T hG₁ hH₁ (i₁ ≫ f ≫ r₁) (divP_comp T i₁ f r₁ hf)
  have h0 : i₁ ≫ f ≫ r₀ = 0 := (PDivGroup.hom_eq_zero_of_isConn_of_isEt p k H₀ G₁ hH₀ hG₁).2 _
  have e1 : i₁ ≫ f = (i₁ ≫ f ≫ r₀) ≫ j₀ + (i₁ ≫ f ≫ r₁) ≫ j₁ := by
    conv_lhs => rw [← Category.comp_id f, ← hH]
    simp only [Preadditive.comp_add, Category.assoc]
  refine ⟨q₀ ≫ g₀ + q₁ ≫ g₁ ≫ j₁, ?_⟩
  conv_lhs => rw [← Category.id_comp f, ← hG]
  rw [Preadditive.add_comp, Category.assoc, Category.assoc, hg₀, e1, h0, hg₁, Limits.zero_comp,
    zero_add, Linear.smul_comp, Linear.comp_smul, Linear.comp_smul, smul_add]

theorem exists_pow_smul_and_faithful : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (G H : PDivGroup p k) (f : G ⟶ H), (∀ n : ℕ, (∀ m, ∃ m', T.map f m = p ^ n • m') →
      ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ n • g) ∧ (T.map f = 0 → f = 0) := by
  intro p _ T k _ _ _ G H f
  have part1 : ∀ (n : ℕ) (f : G ⟶ H), (∀ m, ∃ m', T.map f m = p ^ n • m') →
      ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ n • g := by
    intro n
    induction n with
    | zero => intro f _; exact ⟨f, by rw [pow_zero, one_smul]⟩
    | succ n ih =>
      intro f hf
      obtain ⟨g, rfl⟩ := exists_of_divP T f (fun m => by
        obtain ⟨m', hm'⟩ := hf m
        exact ⟨p ^ n • m', by rw [hm', pow_succ', mul_smul]⟩)
      obtain ⟨g', rfl⟩ := ih g (fun m => by
        obtain ⟨m', hm'⟩ := hf m
        refine ⟨m', eq_of_sub_eq_zero (eq_zero_of_pow_smul' T 1 _ ?_)⟩
        have h := map_pow_smul' T 1 g m
        simp only [pow_one] at h
        rw [pow_one, smul_sub, ← h, hm', pow_succ', mul_smul, sub_self])
      exact ⟨g', by rw [smul_smul, ← pow_succ']⟩
  refine ⟨fun n => part1 n f, fun h0 => ?_⟩
  refine hom_ext_conv fun n => ?_
  obtain ⟨g, rfl⟩ := part1 n f (fun m => ⟨0, by rw [h0, LinearMap.zero_apply, smul_zero]⟩)
  rw [pow_smul_conv, zero_conv]

end GlobalTheory.Dieu.Integrality
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberUnitTranslateEqIdFieldPoints
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InfTranslPts

theorem factor_fst {S K : Type} [CommRing S] [Field K] (w : Sp K ⟶ Sp (DualNumber S)) :
    w = (w ≫ spMap (algebraMap S (DualNumber S))) ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective w
  have hε : ψ.hom (DualNumber.eps : DualNumber S) = 0 := by
    have h : ψ.hom (DualNumber.eps : DualNumber S) * ψ.hom (DualNumber.eps : DualNumber S) = 0 := by
      rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
    exact mul_self_eq_zero.1 h
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  refine RingHom.ext fun x => ?_
  change ψ.hom x = ψ.hom (algebraMap S (DualNumber S) x.fst)
  have hx : x = algebraMap S (DualNumber S) x.fst + algebraMap S (DualNumber S) x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  conv_lhs => rw [hx]
  rw [map_add (f := _), map_mul, hε, mul_zero, add_zero]

theorem transl_field_point {X : Scheme.{0}} (G : Over X) [GrpObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
    (P : tEpsG x0 ⟶ G)
    (hP : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ G).left)
    {K : Type} [Field K] (z : Sp K ⟶ (tEpsG x0 ⊗ G).left) :
    z ≫ (lift (fst (tEpsG x0) G ≫ P) (snd (tEpsG x0) G) ≫ μ[G]).left = z ≫ (snd (tEpsG x0) G).left := by
  let zz : Over.mk (z ≫ (tEpsG x0 ⊗ G).hom) ⟶ tEpsG x0 ⊗ G := Over.homMk z rfl
  let p : tEpsG x0 ⟶ Over.mk x0 := Over.homMk (spMap (algebraMap S (DualNumber S))) rfl
  have h1 : GlobalTheory.VertSpanZero.redOver x0 ≫ P = 1 := Over.OverMorphism.ext hP
  have h2 : zz ≫ fst (tEpsG x0) G = (zz ≫ fst (tEpsG x0) G ≫ p) ≫ GlobalTheory.VertSpanZero.redOver x0 := by
    apply Over.OverMorphism.ext
    have := factor_fst (S := S) (K := K) (z ≫ (fst (tEpsG x0) G).left)
    exact this
  have h3 : zz ≫ fst (tEpsG x0) G ≫ P = 1 := by
    rw [← Category.assoc, h2, Category.assoc, h1, MonObj.comp_one]
  have h4 : zz ≫ ((fst (tEpsG x0) G ≫ P) * snd (tEpsG x0) G) = zz ≫ snd (tEpsG x0) G := by
    rw [MonObj.comp_mul, h3, _root_.one_mul]
  exact congrArg (fun q => q.left) h4

theorem transl_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (S : Type) [CommRing S] (x0 : Sp S ⟶ X) (P : tEpsG x0 ⟶ t.G), spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ P.left = (1 : Over.mk x0 ⟶ t.G).left → ∀ y : (tEpsG x0 ⊗ t.G).left, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ (tEpsG x0 ⊗ t.G).left), y ∈ Set.range z.base ∧ z ≫ (lift (fst (tEpsG x0) t.G ≫ P) (snd (tEpsG x0) t.G) ≫ μ[t.G]).left = z ≫ (snd (tEpsG x0) t.G).left := by
  intro E _ _ _ H X t S _ x0 P hP y
  refine ⟨(tEpsG x0 ⊗ t.G).left.residueField y, inferInstance,
    (tEpsG x0 ⊗ t.G).left.fromSpecResidueField y, ?_, transl_field_point t.G x0 P hP _⟩
  exact ⟨IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply y _⟩

end GlobalTheory.InfTranslPts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqMaximalIdealOfTrdegLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField

namespace GlobalTheory

theorem eq_maximalIdeal_of_trdeg_le (F A : Type) [Field F] [CommRing A] [IsDomain A]
    [IsLocalRing A] [Algebra F A] (hA : Algebra.EssFiniteType F A) (p : Ideal A)
    (hp : p.IsPrime)
    (htr : Algebra.trdeg F (FractionRing (A ⧸ p)) ≤ Algebra.trdeg F (ResidueField A)) :
    p = maximalIdeal A := by
  classical
  by_contra hne
  have hle : p ≤ maximalIdeal A := le_maximalIdeal hp.ne_top
  obtain ⟨a, ham, hap⟩ : ∃ a ∈ maximalIdeal A, a ∉ p := by
    by_contra h
    push_neg at h
    exact hne (le_antisymm hle h)
  haveI := hA
  haveI : Algebra.EssFiniteType F (ResidueField A) :=
    Algebra.EssFiniteType.of_surjective (IsScalarTower.toAlgHom F A (ResidueField A))
      (IsLocalRing.residue_surjective)
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F (ResidueField A)
  haveI : Finite s := finite_of_isTranscendenceBasis hs
  let f : A ⧸ p →ₐ[F] ResidueField A :=
    Ideal.Quotient.liftₐ p (IsScalarTower.toAlgHom F A (ResidueField A)) (fun x hx => by
      simpa [IsLocalRing.residue_eq_zero_iff] using hle hx)
  have hfmk : ∀ x : A, f (Ideal.Quotient.mk p x) = IsLocalRing.residue A x := fun x => rfl
  choose y hy using fun i : s => IsLocalRing.residue_surjective (R := A) i.1
  let z : s → A ⧸ p := fun i => Ideal.Quotient.mk p (y i)
  have hfz : f ∘ z = ((↑) : s → ResidueField A) := by
    funext i
    simp only [Function.comp_apply, z, hfmk, hy]
  have hz : AlgebraicIndependent F z := by
    have h1 := hs.1
    rw [← hfz] at h1
    exact h1.of_comp f
  set b : A ⧸ p := Ideal.Quotient.mk p a with hbdef
  have hb0 : b ≠ 0 := by
    rw [hbdef, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hap
  have hbk : b ∈ RingHom.ker f.toRingHom := by
    rw [RingHom.mem_ker]
    change f (Ideal.Quotient.mk p a) = 0
    rw [hfmk, IsLocalRing.residue_eq_zero_iff]
    exact ham
  have hinj := algebraicIndependent_iff_injective_aeval.mp hs.1
  have htrans : Transcendental (Algebra.adjoin F (Set.range z)) b := by
    intro halg
    apply Ideal.comap_ne_bot_of_algebraic_mem hb0 hbk halg
    rw [eq_bot_iff]
    intro c hc
    rw [Ideal.mem_comap, RingHom.mem_ker] at hc
    have hc2 : (c : A ⧸ p) ∈ (MvPolynomial.aeval (R := F) z).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact c.2
    obtain ⟨g, hg⟩ := hc2
    have h0 : MvPolynomial.aeval ((↑) : s → ResidueField A) g = 0 := by
      rw [← hfz]
      change MvPolynomial.aeval (fun i => f (z i)) g = 0
      rw [← MvPolynomial.comp_aeval_apply]
      change f ((MvPolynomial.aeval z).toRingHom g) = 0
      rw [hg]
      exact hc
    have hg0 : g = 0 := hinj (by rw [h0, map_zero])
    rw [Ideal.mem_bot]
    apply Subtype.ext
    rw [← hg, hg0, map_zero]
    rfl
  have hopt : AlgebraicIndependent F (fun o : Option s => o.elim b z) :=
    AlgebraicIndependent.option_iff.mpr ⟨hz, htrans⟩
  have hopt' := hopt.map' (f := IsScalarTower.toAlgHom F (A ⧸ p) (FractionRing (A ⧸ p)))
    (IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p)))
  have hc1 := hopt'.cardinalMk_le_trdeg
  rw [← hs.cardinalMk_eq_trdeg] at htr
  have hle2 : Cardinal.mk (Option s) ≤ Cardinal.mk s := hc1.trans htr
  obtain ⟨e⟩ := Cardinal.le_def _ _ |>.mp hle2
  haveI := Fintype.ofFinite s
  have := Fintype.card_le_of_embedding e
  rw [Fintype.card_option] at this
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianPartFunctionOfWeightUnitLogDeriv
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn
open GlobalTheory.HeatConn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn.LogDerDesc

theorem exists_app_mul_eq_dE : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) (ν : R), (∀ a (α : Q.X) (V : Y.H.left.Opens) f, IsWt Y α V f → IsWt Y α V (dd a V f)) → IsBasic Y h → ∀ (i : h.J) (α : Q.X) (U : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ U ≤ h.W i → ∀ x : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U), IsUnit x → IsWt Y α _ x → ∃ A : Γ(Q.P.A.left, U), (Y.q.left.app U).hom A * x = dE h ν i _ x := by
  intro R _ _ Q O _ _ _ oa Y n dd D h ν hdd hB i α U hU x hx hxw

  have h1 : IsWt Y α _ (dE h ν i _ x) := by
    unfold dE
    refine WtAlg.isWt_add ((hB i).2.2.2 α U hU x hxw) (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ _) ?_)
    exact WtAlg.isWt_sum _ _ fun a _ => WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ _) (hdd a α _ x hxw)

  have h2 : IsWt Y 0 _ (dE h ν i _ x * ((hx.unit⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)ˣ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U))) := by
    intro S _ φ y y' c a a' ha ha' hV hV' hq hc
    have one : ∀ (b : Sp S ⟶ Y.H.left) (hb : ⊤ ≤ b ⁻¹ᵁ (Y.q.left ⁻¹ᵁ U)),
        valR b _ x * valR b _ ((hx.unit⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)ˣ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)) = 1 := by
      intro b hb
      rw [← WtAlg.valR_mul'' _ _ hb, IsUnit.mul_val_inv, WtAlg.valR_eq' _ _ hb, map_one, map_one]
    have e1 := h1 S φ y y' c a a' ha ha' hV hV' hq hc
    have ex := hxw S φ y y' c a a' ha ha' hV hV' hq hc
    have o := one a hV
    have o' := one a' hV'
    rw [WtAlg.valR_mul'' _ _ hV', WtAlg.valR_mul'' _ _ hV, e1, WtAlg.c_zero y y' c hc, Units.val_one, _root_.one_mul]
    rw [ex] at o'
    linear_combination (-((c α : S)) * valR a _ (dE h ν i _ x) * valR a' _ ((hx.unit⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)ˣ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U))) * o
      + (valR a _ (dE h ν i _ x) * valR a _ ((hx.unit⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)ˣ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U))) * o'

  obtain ⟨A, hA⟩ := AbConst.exists_app_eq Y h2
  refine ⟨A, ?_⟩
  rw [hA, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]

end GlobalTheory.HeatConn.LogDerDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddHomInvariantFieldKillsWeightZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatMod.TorUniq
open GlobalTheory.ZH.CrdCalc (valR_res valR_spMap)
open ReciprocityTheory.ChartRestriction.G.Chart (sp)
open TrivSqZeroExt (inl inr)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (coord coord_comp)
open GlobalTheory.HeatMod.TorField

theorem exists_addHom_of_kills_wt_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ e : Fin n → R, (∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0) → ∃ ℓ : Q.X →+ R, ∀ (α : Q.X) (V : Q.P.A.left.Opens) f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = constFn Y.H.hom _ (ℓ α) * f := by
  intro R _ _ Q O _ _ _ oa Y n v dd hd e he
  obtain ⟨u, hb, hu⟩ := exists_isLieBasis v
  have hc : IsLieComb e u (GlobalTheory.SqZero.lieExp u (fun a => (TrivSqZeroExt.inr (e a) : DualNumber R)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) := (GlobalTheory.SqZero.isLieComb_iff_lieExp e _).2 rfl
  have ht := GlobalTheory.Reg.isTangent_of_isLieComb hb.1 hc
  have hq : GlobalTheory.SqZero.lieExp u (fun a => (TrivSqZeroExt.inr (e a) : DualNumber R)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) ≫ Y.q = 1 :=
    Over.OverMorphism.ext (_root_.GlobalTheory.SpecLocalExt.hom_ext_of_localizationAtPrime _ _ _ _ fun P _ => _root_.GlobalTheory.HeatMod.TorField.lieExp_comp_q_eq_one R Q O oa Y n (fun a => v a) u hb.1 hu dd hd e he _ _)
  obtain ⟨ℓ, hℓ⟩ := _root_.GlobalTheory.HeatMod.TorField.exists_torTan_of_q R Q O oa Y _ ht hq
  refine ⟨ℓ, fun α V f hf => ?_⟩
  show combF Y.H.hom dd e _ f = _
  refine sub_eq_zero.1 (Adjust.eq_zero_of_valR_points _ _ fun S _ g hg => ?_)
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) (g ≫ Y.H.hom)
  let φ : R →+* S := φ'.hom
  have hφ : g ≫ Y.H.hom = spMap φ := hφ'.symm
  letI : Algebra R S := φ.toAlgebra
  let z : sp (R₀ := R) S ⟶ Y.H := Over.homMk g hφ
  let ψ : DualNumber R →ₐ[R] DualNumber S := GlobalTheory.SqZero.dualMap (Algebra.ofId R S)
  have hψ : ∀ a : R, ψ (inr a) = inr (φ a) := fun a => GlobalTheory.SqZero.dualMap_inr _ _
  obtain ⟨a₁, a₂⟩ := valR_spMap (GlobalTheory.SqZero.inlS R S).toRingHom g _ hg
  obtain ⟨b₁, b₂⟩ := valR_prod hu hb.1 hd (fun i => ψ (inr (e i)))
    (fun _ _ => by rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) _ a₁ Finset.univ
  have E0 := congrArg (ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ ≫ ·) hℓ.symm
  simp only [GlobalTheory.SqZero.comp_lieExp, ← Category.assoc] at E0
  rw [GlobalTheory.SqZero.lieExp] at E0
  rw [← E0] at b₁ b₂
  have k := valR_torus_mul Y (S := DualNumber S) (φ := algebraMap R (DualNumber S)) (ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ ≫ torTan ℓ) _
    (coord_torTan ℓ ψ) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) hf a₁ b₁
  have a₃ : ∀ s, valR (A := DualNumber S) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z).left (Y.q.left ⁻¹ᵁ V) s = inl (valR g _ s) := a₂
  have k' := congrArg TrivSqZeroExt.snd ((b₂ f).symm.trans k)
  have hu' : ((Units.map ψ.toRingHom.toMonoidHom (epsUnit (ℓ α)) : (DualNumber S)ˣ) : DualNumber S) = 1 + inr (φ (ℓ α)) := by
    rw [← hψ, ← map_one ψ, ← map_add (f := _)]; rfl
  simp only [a₃, hψ, hu'] at k'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [WtAlg.valR_sub' _ _ hg, WtAlg.valR_mul'' _ _ hg, Adjust.valR_const _ φ g hφ _ hg, combF,
    GlobalTheory.ZH.CrdCalc.valR_eq _ _ hg, map_sum, sub_eq_zero]
  simp only [← GlobalTheory.ZH.CrdCalc.valR_eq _ _ hg, WtAlg.valR_mul'' _ _ hg, Adjust.valR_const _ φ g hφ _ hg]
  simpa [TrivSqZeroExt.snd_sum, _root_.mul_comm] using k'

end GlobalTheory.HeatMod.TorUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisPullbackMatrixInvariantFieldsRaynaud
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.InvFactor

section Lie
variable {R : Type} [CommRing R] {G B : Over (Sp R)} [GrpObj G] [GrpObj B] [IsCommMonObj G] [IsCommMonObj B]

theorem smT_comp (a : R) (v : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G) (φ : G ⟶ B) :
    smT (𝟙 (Sp R)) a (v ≫ φ) = smT (𝟙 (Sp R)) a v ≫ φ := (Category.assoc _ _ _).symm

def lieMap (q : G ⟶ B) [IsMonHom q] : TanM (𝟙 (Sp R)) G →ₗ[R] TanM (𝟙 (Sp R)) B where
  toFun v := ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT (tv v ≫ q) (by rw [smT_comp, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem, MonObj.one_comp])
  map_add' u v := ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext (MonObj.mul_comp (tv u) (tv v) q)
  map_smul' a v := ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext (smT_comp a (tv v) q).symm

end Lie

theorem exists_basis_pull_matrix : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∃ (g : ℕ) (w : Module.Basis (Fin g) R (TanM (𝟙 (Sp R)) Dd.toPre.P.A)) (e : Fin g → Fld Dd.toPre.P.A.left) (P : Matrix (Fin g) (Fin n) R) (Qm : Matrix (Fin n) (Fin g) R), (∀ c, IsInv Dd.toPre.P.A (w c) (e c)) ∧ P * Qm = 1 ∧ ∀ b (V : Dd.toPre.P.A.left.Opens) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V → ∀ f : Γ(Dd.toPre.P.A.left, V), dd b W (pbT Y.q.left f W) = ∑ c, constFn Y.H.hom W (P c b) * pbT Y.q.left (e c V f) W := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd
  have hB : Smooth Dd.toPre.P.A.hom := Dd.toPre.P.isAb.smooth
  obtain ⟨g, ⟨w⟩⟩ := GlobalTheory.RayBasis.exists_basis hB
  choose e he using fun c => GlobalTheory.RayBasis.exists_isInv (w c)
  haveI : IsMonHom Y.q := Y.q_linear.isMonHom
  have hq : Smooth Y.q.left := Y.smooth_q
  let L := lieMap Y.q
  choose s hs using fun c => _root_.GlobalTheory.LieSurjLocal.map_surjective R Y.H Dd.toPre.P.A Y.q hq (w c)
  have hs' : ∀ c, L (s c) = w c := fun c => ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext (hs c)
  refine ⟨g, w, e, Matrix.of fun c b => w.repr (L (v b)) c, Matrix.of fun b c => v.repr (s c) b, he, ?_, ?_⟩
  · ext c c'
    simp only [Matrix.mul_apply, Matrix.of_apply]
    have h1 : w.repr (L (s c')) c = ∑ b, w.repr (L (v b)) c * v.repr (s c') b := by
      conv_lhs => rw [← v.sum_repr (s c')]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, Finset.sum_apply']
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
    rw [← h1, hs', w.repr_self, Matrix.one_apply, Finsupp.single_apply]
    exact if_congr eq_comm rfl rfl
  · intro b V W hW f
    have hu : ∑ c, Matrix.of (fun c b => w.repr (L (v b)) c) c b • w c = L (v b) := w.sum_repr _
    have hinv := _root_.GlobalTheory.Heat.InvComb.isInv_comb R Dd.toPre.P.A g w e he (fun c => Matrix.of (fun c b => w.repr (L (v b)) c) c b)
    rw [hu] at hinv
    rw [_root_.GlobalTheory.Heat.PullField.isInv_pbT_single R Y.H Dd.toPre.P.A Y.q (v b) (L (v b)) (dd b) _ rfl (hdd b) hinv V W hW f, GlobalTheory.KS.pbT_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.KS.pbT_mul, GlobalTheory.KS.pbT_constFn _ _ hW, Over.w Y.q, Matrix.of_apply]

end GlobalTheory.InvFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOfPeriodStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylor_object_of_period : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (D' : PLat D.O D.inv) t Q, 0 < N → N.Coprime p → b.IsType σ ρ → D.Cls N D' t → IsPeriod D' ρ Q → ∃ (o : Obj b N (spMap σ)) (h : _) (hL : _) (e : _), UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e := by
  first | (exact @GlobalTheory.UPel.HT.exists_obj_unifAt_of_period) | (exact GlobalTheory.UPel.HT.exists_obj_unifAt_of_period) | (intros; apply GlobalTheory.UPel.HT.exists_obj_unifAt_of_period <;> assumption)
end

