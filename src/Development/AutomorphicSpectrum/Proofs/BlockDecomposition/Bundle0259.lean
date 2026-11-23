module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0251
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreSections
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

variable {X Y : Scheme.{0}}

def chartFn {L : LB X} {d : ℤ} (s : LB.Sec (pw L d)) (i : L.ι) : Γ(X, L.U i) := s.f i

theorem map_prod_eq_pow_mul {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* B)
    (φ' : A' →+* B) {k : ℕ} (x : Fin k → A) (y : Fin k → A') (g : B)
    (h : ∀ l, φ (x l) = g * φ' (y l)) : φ (∏ l, x l) = g ^ k * φ' (∏ l, y l) := by
  rw [map_prod, map_prod, Finset.prod_congr rfl (fun l _ => h l), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

def secMono {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D) (a : τ → LB.Sec (pw L d))
    (w : Fin k → τ) : LB.Sec (pw L D) where
  f i := ∏ l, chartFn (a (w l)) i
  compat i j := by
    subst h
    have := map_prod_eq_pow_mul (X.presheaf.map (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op).hom
      (X.presheaf.map (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op).hom
      (fun l => chartFn (a (w l)) i) (fun l => chartFn (a (w l)) j)
      ((L.g i j ^ d : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j)) (fun l => (a (w l)).compat i j)
    refine this.trans ?_
    congr 1
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
    rfl

def pullPow {N : LB X} {N' : LB Y} {β : X ⟶ Y} (v : LB.Iso N (N'.pull β)) (t : ℤ) :
    LB.Iso (pw N t) ((pw N' t).pull β) :=
  ⟨fun p => v.s p ^ t⟩

theorem prod_mul_prod_eq {B τ : Type} [CommMonoid B] (φ : τ → B) {k : ℕ} (w₁ w₂ w₃ w₄ : Fin k → τ)
    (hw : Finset.univ.val.map w₁ + Finset.univ.val.map w₂ = Finset.univ.val.map w₃ + Finset.univ.val.map w₄) :
    (∏ l, φ (w₁ l)) * ∏ l, φ (w₂ l) = (∏ l, φ (w₃ l)) * ∏ l, φ (w₄ l) := by
  have key : ∀ w : Fin k → τ, ∏ l, φ (w l) = ((Finset.univ.val.map w).map φ).prod := by
    intro w
    rw [Multiset.map_map]
    rfl
  rw [key, key, key, key, ← Multiset.prod_add, ← Multiset.prod_add, ← Multiset.map_add (f := _), ← Multiset.map_add (f := _), hw]

theorem secMono_mul : ∀ {X : Scheme.{0}} {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D) (a : τ → LB.Sec (pw L d)) (w₁ w₂ w₃ w₄ : Fin k → τ), (Finset.univ.val.map w₁ + Finset.univ.val.map w₂ = Finset.univ.val.map w₃ + Finset.univ.val.map w₄) → ∀ c, (secMono h a w₁).f c * (secMono h a w₂).f c = (secMono h a w₃).f c * (secMono h a w₄).f c := by
  intro X L τ d D k h a w₁ w₂ w₃ w₄ hw c
  exact prod_mul_prod_eq (fun i => chartFn (a i) (show L.ι from c)) w₁ w₂ w₃ w₄ hw

theorem zpow_mul_inv_eq {G : Type} [CommGroup G] (a a' b b' : G) (t : ℤ) (h : a' = a ^ t) (h' : b' = b ^ t) :
    (a * b⁻¹) ^ t = a' * b'⁻¹ := by
  rw [h, h', mul_zpow, inv_zpow]

theorem mapmap_zpow {G H K : Type} [CommGroup G] [CommGroup H] [CommGroup K] (f : G →* H) (g : H →* K)
    (x : G) (t : ℤ) : g (f (x ^ t)) = (g (f x)) ^ t := by
  rw [map_zpow, map_zpow]

theorem pull_pw_g {Z W : Scheme.{0}} (L : LB W) (φ : Z ⟶ W) (t : ℤ) (i j : PUnit → L.ι) :
    ((pw L t).pull φ).g i j = ((L.pull φ).g i j) ^ t := by
  refine (pull_g (pw L t) φ i j).trans ((mapmap_zpow (pullU φ _) (res _) (L.g _ _) t).trans ?_)
  exact congrArg (· ^ t) (pull_g L φ i j).symm

theorem pullPow_isGen : ∀ {X Y : Scheme.{0}} {N : LB X} {N' : LB Y} {β : X ⟶ Y} (v : LB.Iso N (N'.pull β)) (t : ℤ), v.IsGen → (pullPow v t).IsGen := by
  intro X Y N N' β v t hv p q
  have := congrArg (· ^ t) (hv p q)
  simp only [mul_zpow, ← map_zpow] at this
  refine this.trans ?_
  congr 1
  refine zpow_mul_inv_eq (G := Γ(X, (N'.pull β).U p.1 ⊓ N.U p.2 ⊓ ((N'.pull β).U q.1 ⊓ N.U q.2))ˣ)
    (res _ ((N'.pull β).g p.1 q.1)) (res _ (((pw N' t).pull β).g p.1 q.1)) (res _ (N.g p.2 q.2))
    (res _ ((pw N t).g p.2 q.2)) t ?_ ?_
  · exact (congrArg _ (pull_pw_g N' β t p.1 q.1)).trans (map_zpow _ _ _)
  · exact map_zpow _ _ _

theorem secMaps_secMono : ∀ {X Y : Scheme.{0}} {N : LB X} {N' : LB Y} {β : X ⟶ Y} (v : LB.Iso N (N'.pull β)) {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D) (a : τ → LB.Sec (pw N d)) (a' : τ → LB.Sec (pw N' d)), (∀ i, SecMaps (pullPow v d) (a i) (secPull (a' i) β)) → ∀ w : Fin k → τ, SecMaps (pullPow v D) (secMono h a w) (secPull (secMono h a' w) β) := by
  intro X Y N N' β v τ d D k h a a' hmaps w p
  subst h
  let u : Γ(X, (N'.pull β).U p.1 ⊓ N.U p.2)ˣ := v.s p
  refine (map_prod_eq_pow_mul
    ((resG X (inf_le_left)).comp ((resG X (GlobalTheory.Cartier.pull_U N' β p.1).le).comp (β.app _).hom))
    (resG X inf_le_right) (fun l => chartFn (a' (w l)) (p.1 ⟨⟩)) (fun l => chartFn (a (w l)) p.2)
    (u ^ d).val (fun l => hmaps (w l) p)).trans ?_
  congr 1
  rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
  rfl

theorem nonzeroLocus_secMono_const : ∀ {X : Scheme.{0}} {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D) (a : τ → LB.Sec (pw L d)) (i : τ), 1 ≤ k → nonzeroLocus (secMono h a (fun _ => i)) = nonzeroLocus (a i) := by
  intro X L τ d D k h a i hk
  refine iSup_congr fun c => ?_
  change X.basicOpen (∏ l : Fin k, chartFn (a i) c) = X.basicOpen (chartFn (a i) c)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact Scheme.basicOpen_pow _ _ (by omega)

end GlobalTheory.CompanionTheory.FormalAlg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenRestrictionFunctionsCompatible
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct Opposite

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.RingCompat

attribute [local instance] algebraOfOver

lemma topIso_inv_res_hom {X : Scheme.{0}} (V : X.Opens) :
    X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op ≫ V.topIso.inv = V.ι.appTop := by
  rw [Scheme.Opens.topIso_inv, Scheme.Hom.appTop, Scheme.Opens.ι_app]
  exact (X.presheaf.map_comp _ _).symm.trans (congrArg X.presheaf.map (Subsingleton.elim _ _))

lemma topIso_inv_res {X : Scheme.{0}} (V : X.Opens) (c : Γ(X, ⊤)) :
    V.topIso.inv (X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op c) = V.ι.appTop c :=
  ConcreteCategory.congr_hom (topIso_inv_res_hom V) c

lemma appIso_hom_res {Z : Scheme.{0}} (O : Z.Opens) (W : (O : Scheme.{0}).Opens) (d : Γ(Z, ⊤)) :
    (O.ι.appIso W).hom (Z.presheaf.map (homOfLE le_top : O.ι ''ᵁ W ⟶ ⊤).op d) =
      (O : Scheme.{0}).presheaf.map (homOfLE le_top : W ⟶ ⊤).op (O.ι.appTop d) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.appIso_hom',
    Scheme.Hom.map_appLE]
  rfl

lemma morphismRestrict_appTop_ι {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) (c : Γ(X, ⊤)) :
    (φ ∣_ V).appTop (V.ι.appTop c) = (φ ⁻¹ᵁ V).ι.appTop (φ.appTop c) := by
  have h := congrArg Scheme.Hom.appTop (morphismRestrict_ι φ V)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h c

lemma overBase_appTop {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V)
    (b : Γ(X, V)) :
    (φ ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv b) =
      (φ ∣_ V).appTop (V.topIso.inv b) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, IsAffineOpen.isoSpec_hom_appTop,
    CommRingCat.comp_apply]
  erw [Iso.inv_hom_id_apply]

theorem toFunctions_preimage : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X), φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)], letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩; ∀ (W : (φ ⁻¹ᵁ V).toScheme.Opens) (a : A), ((φ ⁻¹ᵁ V).ι.appIso W).hom (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ W) a) = toFunctions (A := Γ(X, V)) W (toFunctions (A := A) V a) := by
  intro A _ _ X Z _ _ φ hφ V hV _ W a
  have hZ : (Z ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a) =
      φ.appTop ((X ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a)) := by
    rw [← hφ, Scheme.Hom.comp_appTop]
    rfl
  change ((φ ⁻¹ᵁ V).ι.appIso W).hom (Z.presheaf.map (homOfLE le_top).op
      ((Z ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a))) =
    (φ ⁻¹ᵁ V).toScheme.presheaf.map (homOfLE le_top).op
      ((φ ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv
        (X.presheaf.map (homOfLE le_top).op
          ((X ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a)))))
  rw [overBase_appTop, topIso_inv_res, morphismRestrict_appTop_ι, hZ, appIso_hom_res]

end GlobalTheory.CompanionTheory.GE.RingCompat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodProductFiltrationLevels
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem prod_eq_t_mul_unit_count : ∀ {l : ℕ} [Fact l.Prime] {ι : Type} (s : Finset ι) (t : ι → Formalism.Per6.BdRp l) (i₀ : ι), i₀ ∈ s →
    ∀ u : (Formalism.Per6.BdRp l)ˣ, ∏ μ ∈ s, t μ = GroundTheory.PAdicHodge.tBdR l * (u : Formalism.Per6.BdRp l) →
      thB l (t i₀) = 0 →
      ∀ μ ∈ s, (μ = i₀ → t μ ∉ FB l 2) ∧ (μ ≠ i₀ → t μ ∉ FB l 1) := by
  intro l _ ι s t i₀ hi₀ u hprod h0 μ hμ
  have hmax : IsLocalRing.maximalIdeal (Formalism.Per6.BdRp l) = Ideal.span {GroundTheory.PAdicHodge.tBdR l} :=
    GroundTheory.PAdicHodge.maximalIdeal_eq_span_fontaineT GroundTheory.PAdicHodge.untilt_epsilon
      GroundTheory.PAdicHodge.untilt_frobeniusEquiv_symm_epsilon_ne_one
  have htirr : Irreducible (GroundTheory.PAdicHodge.tBdR l) :=
    IsDiscreteValuationRing.irreducible_iff_uniformizer _ |>.2 hmax
  have hFB : ∀ k, FB l k = Ideal.span {GroundTheory.PAdicHodge.tBdR l ^ k} := fun k => by
    rw [FB, ker_thB_eq, hmax, Ideal.span_singleton_pow]
  have hnot : ¬ (GroundTheory.PAdicHodge.tBdR l ^ 2 ∣ ∏ μ ∈ s, t μ) := by
    rw [hprod, pow_two]
    intro h
    have h1 : GroundTheory.PAdicHodge.tBdR l ∣ (u : Formalism.Per6.BdRp l) :=
      (mul_dvd_mul_iff_left htirr.ne_zero).1 h
    exact htirr.not_isUnit (isUnit_of_dvd_unit h1 u.isUnit)
  have hi : GroundTheory.PAdicHodge.tBdR l ∣ t i₀ := by
    have : t i₀ ∈ FB l 1 := by
      rw [FB, pow_one, RingHom.mem_ker]; exact h0
    rw [hFB, pow_one] at this
    exact Ideal.mem_span_singleton.1 this
  refine ⟨fun e hm => hnot ?_, fun hne hm => hnot ?_⟩
  · subst e
    rw [hFB] at hm
    exact (Ideal.mem_span_singleton.1 hm).trans (Finset.dvd_prod_of_mem t hμ)
  · rw [hFB, pow_one] at hm
    have hd := Ideal.mem_span_singleton.1 hm
    have hμ' : μ ∈ s.erase i₀ := Finset.mem_erase.2 ⟨hne, hμ⟩
    rw [← Finset.mul_prod_erase s t hi₀, ← Finset.mul_prod_erase (s.erase i₀) t hμ', pow_two, ← mul_assoc]
    exact (mul_dvd_mul hi hd).mul_right _

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalPrimeCriterion
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Krull

theorem stalkMap_germ_appLE {Y Z : Scheme.{0}} (ψ : Z ⟶ Y) (W : Y.Opens) (U : Z.Opens)
    (h : U ≤ ψ ⁻¹ᵁ W) (z : Z) (hz : z ∈ U) (hy : ψ z ∈ W) (a : Γ(Y, W)) :
    ψ.stalkMap z (Y.presheaf.germ W (ψ z) hy a) = Z.presheaf.germ U z hz (ψ.appLE W U h a) := by
  simp [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, TopCat.Presheaf.germ_res_apply]

theorem isUnit_germ_fromSpec {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(Z, U)) (hz : hU.fromSpec q ∈ U) (c : Γ(Z, U)) :
    IsUnit (Z.presheaf.germ U _ hz c) ↔ c ∉ q.asIdeal := by
  letI : Algebra Γ(Z, U) (Z.presheaf.stalk (hU.fromSpec q)) := (Z.presheaf.germ U _ hz).hom.toAlgebra
  haveI : IsLocalization.AtPrime (Z.presheaf.stalk (hU.fromSpec q)) q.asIdeal := hU.isLocalization_stalk' q hz
  rw [← Ideal.mem_primeCompl_iff]
  exact IsLocalization.AtPrime.isUnit_to_map_iff (Z.presheaf.stalk (hU.fromSpec q)) q.asIdeal c

theorem exists_mul_eq_of_germ_eq {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(Z, U)) (hz : hU.fromSpec q ∈ U) (c d : Γ(Z, U))
    (e : Z.presheaf.germ U _ hz c = Z.presheaf.germ U _ hz d) :
    ∃ v : Γ(Z, U), v ∉ q.asIdeal ∧ v * c = v * d := by
  letI : Algebra Γ(Z, U) (Z.presheaf.stalk (hU.fromSpec q)) := (Z.presheaf.germ U _ hz).hom.toAlgebra
  haveI : IsLocalization.AtPrime (Z.presheaf.stalk (hU.fromSpec q)) q.asIdeal := hU.isLocalization_stalk' q hz
  obtain ⟨⟨v, hv⟩, hvcd⟩ :=
    (IsLocalization.eq_iff_exists q.asIdeal.primeCompl (Z.presheaf.stalk (hU.fromSpec q))).mp e
  exact ⟨v, hv, hvcd⟩

theorem exists_frac_stalk {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) (y : Y) (hy : y ∈ W)
    (s : Y.presheaf.stalk y) :
    ∃ a u : Γ(Y, W), IsUnit (Y.presheaf.germ W y hy u) ∧
      s * Y.presheaf.germ W y hy u = Y.presheaf.germ W y hy a := by
  letI : Algebra Γ(Y, W) (Y.presheaf.stalk y) := (Y.presheaf.germ W y hy).hom.toAlgebra
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hW.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hW.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨⟨a, u⟩, hs⟩ := IsLocalization.surj (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl s
  exact ⟨a, u.1, IsLocalization.map_units (Y.presheaf.stalk y) u, hs⟩

theorem exists_mul_eq_zero_of_germ {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) (y : Y)
    (hy : y ∈ W) (a : Γ(Y, W)) (e : Y.presheaf.germ W y hy a = 0) :
    ∃ u : Γ(Y, W), IsUnit (Y.presheaf.germ W y hy u) ∧ u * a = 0 := by
  letI : Algebra Γ(Y, W) (Y.presheaf.stalk y) := (Y.presheaf.germ W y hy).hom.toAlgebra
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hW.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hW.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨⟨u, hu⟩, hua⟩ :=
    (IsLocalization.map_eq_zero_iff (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y) a).mp e
  exact ⟨u, IsLocalization.map_units (Y.presheaf.stalk y) (⟨u, hu⟩ : (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl), hua⟩

theorem isIso_stalkMap_of_isIso_restrict {Y Z : Scheme.{0}} (ψ : Z ⟶ Y) (W : Y.Opens)
    (h : IsIso (ψ ∣_ W)) (z : Z) (hz : z ∈ ψ ⁻¹ᵁ W) : IsIso (ψ.stalkMap z) := by
  haveI : IsIso ((ψ ∣_ W).stalkMap ⟨z, hz⟩) := by
    first
    | infer_instance
    | (haveI : IsOpenImmersion (ψ ∣_ W) := inferInstance; infer_instance)
    | (haveI : IsOpenImmersion (ψ ∣_ W) := IsOpenImmersion.of_isIso _; infer_instance)
    | exact PresheafedSpace.IsOpenImmersion.stalk_iso (ψ ∣_ W).toPshHom ⟨z, hz⟩
  have e := morphismRestrictStalkMap ψ W ⟨z, hz⟩
  show IsIso (ψ.stalkMap (⟨z, hz⟩ : (ψ ⁻¹ᵁ W : Z.Opens)).1)
  rw [Arrow.iso_w' e]
  infer_instance

theorem chart_fractions_of_isIso_stalkMap {Y Z : Scheme.{0}} (ψ : Z ⟶ Y) {W : Y.Opens}
    (hW : IsAffineOpen W) {U : Z.Opens} (hU : IsAffineOpen U) (h : U ≤ ψ ⁻¹ᵁ W)
    (q : PrimeSpectrum Γ(Z, U)) (hz : hU.fromSpec q ∈ U) (hiso : IsIso (ψ.stalkMap (hU.fromSpec q))) :
    (∀ c : Γ(Z, U), ∃ a u : Γ(Y, W), ψ.appLE W U h u ∉ q.asIdeal ∧
      ∃ v : Γ(Z, U), v ∉ q.asIdeal ∧ v * (ψ.appLE W U h u * c) = v * ψ.appLE W U h a) ∧
    (∀ a : Γ(Y, W), (∃ v : Γ(Z, U), v ∉ q.asIdeal ∧ v * ψ.appLE W U h a = 0) →
      ∃ u : Γ(Y, W), ψ.appLE W U h u ∉ q.asIdeal ∧ u * a = 0) := by
  have hy : ψ (hU.fromSpec q) ∈ W := h hz
  have hbij := (ConcreteCategory.isIso_iff_bijective (ψ.stalkMap (hU.fromSpec q))).mp hiso
  constructor
  · intro c
    obtain ⟨s, hs0⟩ := hbij.2 (Z.presheaf.germ U _ hz c)
    obtain ⟨a, u, hu, hs⟩ := exists_frac_stalk hW (ψ (hU.fromSpec q)) hy s
    have hs' := congrArg (ψ.stalkMap (hU.fromSpec q)) hs
    rw [map_mul, hs0, stalkMap_germ_appLE ψ W U h _ hz hy u, stalkMap_germ_appLE ψ W U h _ hz hy a] at hs'
    have hu' : IsUnit (Z.presheaf.germ U _ hz (ψ.appLE W U h u)) := by
      rw [← stalkMap_germ_appLE ψ W U h _ hz hy u]
      exact hu.map _
    rw [isUnit_germ_fromSpec hU q hz] at hu'
    refine ⟨a, u, hu', ?_⟩
    apply exists_mul_eq_of_germ_eq hU q hz
    rw [map_mul, mul_comm, hs']
  · rintro a ⟨v, hv, hva⟩
    have h0 : Z.presheaf.germ U _ hz (ψ.appLE W U h a) = 0 := by
      have hvu : IsUnit (Z.presheaf.germ U _ hz v) := (isUnit_germ_fromSpec hU q hz v).mpr hv
      have hh := congrArg (Z.presheaf.germ U _ hz) hva
      rw [map_mul, map_zero] at hh
      exact hvu.mul_right_eq_zero.mp hh
    have h1 : Y.presheaf.germ W _ hy a = 0 := by
      apply hbij.1
      rw [map_zero, stalkMap_germ_appLE ψ W U h _ hz hy a, h0]
    obtain ⟨u, hu, hua⟩ := exists_mul_eq_zero_of_germ hW _ hy a h1
    refine ⟨u, ?_, hua⟩
    rw [← isUnit_germ_fromSpec hU q hz, ← stalkMap_germ_appLE ψ W U h _ hz hy u]
    exact hu.map _

theorem chart_fractions_subscheme {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}}
    (ψ : Z ⟶ J.subscheme) (V : X.Opens) (hV : IsAffineOpen V) (f : Γ(X, V))
    (hiso : IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f))) (U : Z.Opens) (hU : IsAffineOpen U)
    (h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V) (q : Ideal Γ(Z, U)) (hq : q.IsPrime)
    (hf : (ψ ≫ J.subschemeι).appLE V U h f ∉ q) :
    (∀ c : Γ(Z, U), ∃ b t : Γ(X, V), (ψ ≫ J.subschemeι).appLE V U h t ∉ q ∧
      ∃ v : Γ(Z, U), v ∉ q ∧ v * ((ψ ≫ J.subschemeι).appLE V U h t * c) =
        v * (ψ ≫ J.subschemeι).appLE V U h b) ∧
    (∀ b : Γ(X, V), (∃ v : Γ(Z, U), v ∉ q ∧ v * (ψ ≫ J.subschemeι).appLE V U h b = 0) →
      ∃ t : Γ(X, V), (ψ ≫ J.subschemeι).appLE V U h t ∉ q ∧ t * b ∈ J.ideal ⟨V, hV⟩) := by
  let p : PrimeSpectrum Γ(Z, U) := ⟨q, hq⟩
  have hz : hU.fromSpec p ∈ (U : Set Z) := by
    rw [← hU.range_fromSpec]
    exact Set.mem_range_self _
  have hunit : IsUnit (Z.presheaf.germ U _ hz ((ψ ≫ J.subschemeι).appLE V U h f)) :=
    (isUnit_germ_fromSpec hU p hz _).mpr hf
  have hb : hU.fromSpec p ∈ Z.basicOpen ((ψ ≫ J.subschemeι).appLE V U h f) :=
    (Z.mem_basicOpen _ _ hz).mpr hunit
  have e1 : Z.basicOpen ((ψ ≫ J.subschemeι).appLE V U h f) =
      U ⊓ Z.basicOpen ((ψ ≫ J.subschemeι).app V f) := Z.basicOpen_res _ (homOfLE h).op
  have hb2 : hU.fromSpec p ∈ Z.basicOpen ((ψ ≫ J.subschemeι).app V f) :=
    (TopologicalSpace.Opens.mem_inf.mp (e1 ▸ hb)).2
  have e2 := Scheme.preimage_basicOpen (ψ ≫ J.subschemeι) f
  have hmem : hU.fromSpec p ∈ ψ ⁻¹ᵁ (J.subschemeι ⁻¹ᵁ X.basicOpen f) := by
    have hh : hU.fromSpec p ∈ (ψ ≫ J.subschemeι) ⁻¹ᵁ X.basicOpen f := e2 ▸ hb2
    exact hh
  have hist : IsIso (ψ.stalkMap (hU.fromSpec p)) := isIso_stalkMap_of_isIso_restrict ψ _ hiso _ hmem
  have hW' : IsAffineOpen (J.subschemeι ⁻¹ᵁ V) := hV.preimage J.subschemeι
  obtain ⟨H1, H2⟩ := chart_fractions_of_isIso_stalkMap ψ hW' hU h p hz hist
  have hce : ∀ t : Γ(X, V), (ψ ≫ J.subschemeι).appLE V U h t =
      ψ.appLE (J.subschemeι ⁻¹ᵁ V) U h (J.subschemeι.app V t) := by
    intro t
    rw [Scheme.Hom.comp_appLE]
    rfl
  have hsurj := J.subschemeι_app_surjective ⟨V, hV⟩
  constructor
  · intro c
    obtain ⟨a, u, hu, v, hv, hvc⟩ := H1 c
    obtain ⟨b, rfl⟩ := hsurj a
    obtain ⟨t, rfl⟩ := hsurj u
    refine ⟨b, t, ?_, v, hv, ?_⟩
    · rw [hce]
      exact hu
    · rw [hce, hce]
      exact hvc
  · rintro b ⟨v, hv, hvb⟩
    rw [hce] at hvb
    obtain ⟨u, hu, hub⟩ := H2 (J.subschemeι.app V b) ⟨v, hv, hvb⟩
    obtain ⟨t, rfl⟩ := hsurj u
    refine ⟨t, ?_, ?_⟩
    · rw [hce]
      exact hu
    · rw [← J.ker_subschemeι_app ⟨V, hV⟩, RingHom.mem_ker, map_mul]
      exact hub

theorem stalk_over_isoLocus : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme) (V : X.Opens) (hV : IsAffineOpen V) (f : Γ(X, V)), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V, letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∀ q : Ideal Γ(Z, U), q.IsPrime → f ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) → (∀ c : Γ(Z, U), ∃ b t : Γ(X, V), t ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) ∧ ∃ v : Γ(Z, U), v ∉ q ∧ v * (algebraMap Γ(X, V) Γ(Z, U) t * c) = v * algebraMap Γ(X, V) Γ(Z, U) b) ∧ (∀ b : Γ(X, V), (∃ v : Γ(Z, U), v ∉ q ∧ v * algebraMap Γ(X, V) Γ(Z, U) b = 0) → ∃ t : Γ(X, V), t ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) ∧ t * b ∈ J.ideal ⟨V, hV⟩) := by
  intro X J Z ψ V hV f hiso U hU h q hq hf
  exact chart_fractions_subscheme J ψ V hV f hiso U hU h q hq hf

end GlobalTheory.CompanionTheory.GE.Krull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPushforwardCoherent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh TensorProduct
open TopologicalSpace Opposite

namespace GlobalTheory.CompanionTheory.GE.PushCoh

abbrev overAffine {X Z : Scheme.{0}} (φ : Z ⟶ X) {V : X.Opens} (hV : IsAffineOpen V) :
    (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) :=
  ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩

attribute [local instance] algebraOfOver

lemma algebraMap_overAffine {X Z : Scheme.{0}} (φ : Z ⟶ X) {V : X.Opens} (hV : IsAffineOpen V)
    (b : Γ(X, V)) :
    letI := overAffine φ hV
    Z.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op
      (algebraMap Γ(X, V) Γ((φ ⁻¹ᵁ V).toScheme, ⊤) b : Γ(Z, (φ ⁻¹ᵁ V).ι ''ᵁ ⊤)) =
      φ.app V b := by
  letI := overAffine φ hV
  have s1 : algebraMap Γ(X, V) Γ((φ ⁻¹ᵁ V).toScheme, ⊤) b = (φ ∣_ V).appTop (V.topIso.inv b) := by
    change (φ ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv b) = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, IsAffineOpen.isoSpec_hom_appTop,
      CommRingCat.comp_apply]
    erw [Iso.inv_hom_id_apply]
  rw [s1]
  erw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, CommRingCat.comp_apply]
  refine (RelSerre.app_eqToHom_apply φ (Scheme.Opens.ι_image_top V) _ _ b).trans ?_
  simp

def zerothCohomologyToSections {X Z : Scheme.{0}} (φ : Z ⟶ X) {V : X.Opens} (hV : IsAffineOpen V) (M : Z.Modules) :
    letI := overAffine φ hV
    Sheaf.H.{0} (modulesAb (M.restrict (φ ⁻¹ᵁ V).ι)) 0 →ₗ[Γ(X, V)]
      Γ((Scheme.Modules.pushforward φ).obj M, V) :=
  letI := overAffine φ hV
  { toFun := fun x => M.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op
      (Sheaf.H.equiv₀ (modulesAb (M.restrict (φ ⁻¹ᵁ V).ι)) isTerminalTop x :
        Γ(M, (φ ⁻¹ᵁ V).ι ''ᵁ ⊤))
    map_add' := fun x y => by
      rw [map_add (f := _)]
      exact map_add _ _ _
    map_smul' := fun b x => by
      rw [H.smul_def, ← Sheaf.H.equiv₀_naturality]
      refine (RelSerre.smul_restrict_top M (φ ⁻¹ᵁ V) _ _).trans ?_
      refine (congrArg (· • _) (algebraMap_overAffine φ hV b)).trans ?_
      exact (smul_pushforward φ M b _).symm }

lemma zeroth_cohomology_to_sections_surjective {X Z : Scheme.{0}} (φ : Z ⟶ X) {V : X.Opens} (hV : IsAffineOpen V)
    (M : Z.Modules) : Function.Surjective (zerothCohomologyToSections φ hV M) := by
  letI := overAffine φ hV
  exact ((ConcreteCategory.bijective_of_isIso (M.presheaf.map
    (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op)).comp
    (Sheaf.H.equiv₀ (modulesAb (M.restrict (φ ⁻¹ᵁ V).ι)) isTerminalTop).bijective).2

theorem isCoherent_pushforward_of_isProper {X Z : Scheme.{0}} [IsLocallyNoetherian X] (φ : Z ⟶ X)
    (hφ : IsProper φ) {G : Z.Modules} (hG : IsCoherent G) :
    IsCoherent ((Scheme.Modules.pushforward φ).obj G) := by
  haveI := hG.1
  refine ⟨isQuasicoherent_pushforward_of_qcqs φ G, fun V hV => ?_⟩
  letI := overAffine φ hV
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : IsProper ((φ ⁻¹ᵁ V).toScheme ↘ Spec (.of Γ(X, V))) := by
    change IsProper (φ ∣_ V ≫ hV.isoSpec.hom)
    infer_instance
  have hfin := finite_H_of_isProper (A := Γ(X, V)) (G.restrict (φ ⁻¹ᵁ V).ι) (hG.restrict _) 0
  exact Module.Finite.of_surjective (zerothCohomologyToSections φ hV G) (zeroth_cohomology_to_sections_surjective φ hV G)

end GlobalTheory.CompanionTheory.GE.PushCoh

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SenUnramifiedCharacterPeriodStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sen_unramified_character_period : ∀ {l : ℕ} [Fact l.Prime], ∀ (E : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥E] (ψ : Gal(Om l/↥E) →* ℤ_[l]ˣ), Continuous ψ →
      (∀ σ, GroundTheory.LocalField.unramifiedDegree ↥E (Om l) σ = 1 → ψ σ = 1) →
      ∃ f : ℕ, 0 < f ∧ ∃ x : ℂ_[l], x ≠ 0 ∧ ∀ σ : Gal(Om l/↥E),
        σ • x = algebraMap ℚ_[l] ℂ_[l] ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f) * x := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.exists_pow_eigenvector_of_unramified_units | exact GlobalTheory.CompanionTheory.LTPer.exists_pow_eigenvector_of_unramified_units | (intros; apply GlobalTheory.CompanionTheory.LTPer.exists_pow_eigenvector_of_unramified_units <;> assumption)
end
end

