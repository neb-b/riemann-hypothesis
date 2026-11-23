module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import ReciprocityTheory.SemistableReduction.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0335
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourTermComplexQuasiIsoAtFormalProperties
section
set_option autoImplicit false

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.QAtFormal

universe u

variable {C : Type u} [Category.{0} C] (K : Cx C)

theorem qAt_ident (T : C) : K.QAt (𝟙 T) := by
  refine ⟨fun x _ h => ?_, fun y hy => ⟨y, hy, ?_⟩, fun x y _ h => ⟨y, ?_⟩, fun y hy => ⟨y, 0, hy, ?_⟩,
    fun x y _ h => ⟨y, ?_⟩, fun y hy => ⟨y, 0, hy, ?_⟩⟩
  · rwa [K.M0.map_id] at h
  · exact K.M0.map_id T y
  · rw [K.M1.map_id] at h; exact h.symm
  · rw [K.M1.map_id, map_zero, add_zero]
  · rw [K.M2.map_id] at h; exact h.symm
  · rw [K.M2.map_id, map_zero, add_zero]

theorem qAt_comp {T T' T'' : C} (a : T ⟶ T') (b : T' ⟶ T'') (ha : K.QAt a) (hb : K.QAt b) :
    K.QAt (a ≫ b) := by
  refine ⟨fun x hx h => ?_, fun y hy => ?_, fun x y hx h => ?_, fun y hy => ?_,
    fun x y hx h => ?_, fun y hy => ?_⟩
  · rw [K.M0.map_comp] at h
    exact ha.inj0 x hx (hb.inj0 _ (by rw [K.diffZero_natural, hx, map_zero]) h)
  · obtain ⟨x', hx', rfl⟩ := hb.surj0 y hy
    obtain ⟨x, hx, rfl⟩ := ha.surj0 x' hx'
    exact ⟨x, hx, K.M0.map_comp a b x⟩
  · rw [K.M1.map_comp] at h
    obtain ⟨w', hw'⟩ := hb.inj1 _ y (by rw [K.diffOne_natural, hx, map_zero]) h
    exact ha.inj1 x w' hx hw'.symm
  · obtain ⟨x', w', hx', rfl⟩ := hb.surj1 y hy
    obtain ⟨x, w, hx, rfl⟩ := ha.surj1 x' hx'
    refine ⟨x, K.M0.map b w + w', hx, ?_⟩
    simp only [map_add (f := _), K.M1.map_comp, K.diffZero_natural]
    abel
  · rw [K.M2.map_comp] at h
    obtain ⟨w', hw'⟩ := hb.inj2 _ y (by rw [K.diffTwo_natural, hx, map_zero]) h
    exact ha.inj2 x w' hx hw'.symm
  · obtain ⟨x', w', hx', rfl⟩ := hb.surj2 y hy
    obtain ⟨x, w, hx, rfl⟩ := ha.surj2 x' hx'
    refine ⟨x, K.M1.map b w + w', hx, ?_⟩
    simp only [map_add (f := _), K.M2.map_comp, K.diffOne_natural]
    abel

theorem qAt_of_comp_retract {T T' T'' : C} (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T')
    (hbc : b ≫ c = 𝟙 T') (h : K.QAt (a ≫ b)) : K.QAt a := by
  have e0 : ∀ y, K.M0.map c (K.M0.map b y) = y := fun y => by
    rw [← K.M0.map_comp, hbc, K.M0.map_id]
  have e1 : ∀ y, K.M1.map c (K.M1.map b y) = y := fun y => by
    rw [← K.M1.map_comp, hbc, K.M1.map_id]
  have e2 : ∀ y, K.M2.map c (K.M2.map b y) = y := fun y => by
    rw [← K.M2.map_comp, hbc, K.M2.map_id]
  refine ⟨fun x hx hax => ?_, fun y hy => ?_, fun x y hx hxy => ?_, fun y hy => ?_,
    fun x y hx hxy => ?_, fun y hy => ?_⟩
  · exact h.inj0 x hx (by rw [K.M0.map_comp, hax, map_zero])
  · obtain ⟨x, hx, hxy⟩ := h.surj0 (K.M0.map b y) (by rw [K.diffZero_natural, hy, map_zero])
    refine ⟨x, hx, ?_⟩
    rw [K.M0.map_comp] at hxy
    simpa only [e0] using congrArg (K.M0.map c) hxy
  · exact h.inj1 x (K.M0.map b y) hx (by rw [K.M1.map_comp, hxy, K.diffZero_natural])
  · obtain ⟨x, w, hx, hw⟩ := h.surj1 (K.M1.map b y) (by rw [K.diffOne_natural, hy, map_zero])
    refine ⟨x, K.M0.map c w, hx, ?_⟩
    have := congrArg (K.M1.map c) hw
    rw [map_add (f := _), K.M1.map_comp, e1, e1, ← K.diffZero_natural] at this
    exact this
  · exact h.inj2 x (K.M1.map b y) hx (by rw [K.M2.map_comp, hxy, K.diffOne_natural])
  · obtain ⟨x, w, hx, hw⟩ := h.surj2 (K.M2.map b y) (by rw [K.diffTwo_natural, hy, map_zero])
    refine ⟨x, K.M1.map c w, hx, ?_⟩
    have := congrArg (K.M2.map c) hw
    rw [map_add (f := _), K.M2.map_comp, e2, e2, ← K.diffOne_natural] at this
    exact this

theorem qAt_of_isIso {T T' : C} (a : T ⟶ T') [IsIso a] : K.QAt a :=
  qAt_of_comp_retract K a (inv a) a (IsIso.inv_hom_id a) (by rw [IsIso.hom_inv_id]; exact qAt_ident K T)

theorem qAt_formal : ∀ (C : Type 1) [Category.{0} C] (K : Cx C),
    (∀ (T T' : C) (a : T ⟶ T') [IsIso a], K.QAt a) ∧
    (∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), K.QAt a → K.QAt b → K.QAt (a ≫ b)) ∧
    ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T'), b ≫ c = 𝟙 T' → K.QAt (a ≫ b) → K.QAt a :=
  fun _ _ K => ⟨fun _ _ a _ => qAt_of_isIso K a, fun _ _ _ a b => qAt_comp K a b,
    fun _ _ _ a b c => qAt_of_comp_retract K a b c⟩

end GlobalTheory.CxCoh.QAtFormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameSectionSliceEqPolyDivDetPow
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem differentiable_det_of {r : ℕ} :
    Differentiable ℂ (fun y : Fin r → Fin r → ℂ => (Matrix.of y).det) := by
  have : (fun y : Fin r → Fin r → ℂ => (Matrix.of y).det) =
      fun y => ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℂ) * ∏ i, y (σ i) i := by
    funext y
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    simp [Matrix.of_apply]
  rw [this]
  fun_prop

theorem differentiable_update_frame {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {r : ℕ}
    (x : Ψ → Fin r → Fin r → ℂ) (τ : Ψ) :
    Differentiable ℂ (fun y : Fin r → Fin r → ℂ => Function.update x τ y) := by
  intro y
  exact (hasFDerivAt_update x y).differentiableAt

end GlobalTheory

namespace GlobalTheory

theorem section_slice_eq_poly_div_det_pow :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) [DecidableEq X.Ψ],
      (∀ x : Frame X.Ψ r, x ∈ X.dom ↔ ∀ τ, (mat x τ).det ≠ 0) →
      ∀ (la : Wt X.Ψ r) (N : ℕ), (∀ τ i, 0 ≤ la τ i + N) →
      ∀ P : Frame X.Ψ r → ℂ, X.IsSec la P → ∀ x ∈ X.dom, ∀ τ : X.Ψ,
        ∃ F : MvPolynomial (Fin r × Fin r) ℂ, F.IsHomogeneous (∑ i, (la τ i + N).toNat) ∧
          ∀ y : Fin r → Fin r → ℂ, (Matrix.of y).det ≠ 0 →
            P (Function.update x τ y) =
              MvPolynomial.eval (fun ij => y ij.1 ij.2) F * ((Matrix.of y).det)⁻¹ ^ N := by
  intro E _ _ _ r X _ hdom la N hN P hP x hx τ
  classical

  have hupd : ∀ y : Fin r → Fin r → ℂ,
      Function.update x τ y ∈ X.dom ↔ (Matrix.of y).det ≠ 0 := by
    intro y
    rw [hdom]
    have hx' := (hdom x).1 hx
    constructor
    · intro h
      have := h τ
      simpa [mat] using this
    · intro h σ
      by_cases hσ : σ = τ
      · subst hσ
        simpa [mat] using h
      · simpa [mat, Function.update_of_ne hσ] using hx' σ
  let a : Fin r → ℕ := fun i => (la τ i + N).toNat
  let h : Matrix (Fin r) (Fin r) ℂ → ℂ := fun y =>
    P (Function.update x τ (fun i j => y i j)) * y.det ^ N

  have hholo : ReciprocityTheory.MultiplicativeHeights.IsHoloGL h := by
    unfold ReciprocityTheory.MultiplicativeHeights.IsHoloGL
    have h1 : DifferentiableOn ℂ (fun y : Fin r → Fin r → ℂ => P (Function.update x τ y))
        {y | (Matrix.of y).det ≠ 0} :=
      hP.1.comp (differentiable_update_frame x τ).differentiableOn
        (fun y hy => (hupd y).2 hy)
    have h2 : DifferentiableOn ℂ (fun y : Fin r → Fin r → ℂ => (Matrix.of y).det ^ N)
        {y | (Matrix.of y).det ≠ 0} :=
      (differentiable_det_of.pow N).differentiableOn
    exact h1.mul h2

  have htri : ReciprocityTheory.MultiplicativeHeights.IsTriEquivariant a h := by
    intro y b hy hb hbt
    let b' : Frame X.Ψ r := fun σ => if σ = τ then b else (1 : Matrix (Fin r) (Fin r) ℂ)
    have hbτ : b' τ = b := by exact if_pos rfl
    have hbσ : ∀ σ, σ ≠ τ → b' σ = (1 : Matrix (Fin r) (Fin r) ℂ) := fun σ hσ => by exact if_neg hσ
    have hb'B : b' ∈ Bor X.Ψ r := by
      intro σ
      by_cases hσ : σ = τ
      · subst hσ
        refine ⟨?_, fun c d hcd => ?_⟩
        · change (Matrix.of (b' σ)).det ≠ 0
          rw [hbτ]; exact hb
        · rw [hbτ]; exact hbt hcd
      · refine ⟨?_, fun c d hcd => ?_⟩
        · change (Matrix.of (b' σ)).det ≠ 0
          rw [hbσ σ hσ]; change (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0; simp
        · rw [hbσ σ hσ, Matrix.one_apply, if_neg (ne_of_lt hcd).symm]
    have hrm : rmul (Function.update x τ (fun i j => y i j)) b' =
        Function.update x τ (fun i j => (y * b) i j) := by
      funext σ
      by_cases hσ : σ = τ
      · subst hσ
        change (Matrix.of (Function.update x σ (fun i j => y i j) σ) * Matrix.of (b' σ) :
          Matrix (Fin r) (Fin r) ℂ) = Function.update x σ (fun i j => (y * b) i j) σ
        rw [hbτ, Function.update_self, Function.update_self]
        rfl
      · change (Matrix.of (Function.update x τ (fun i j => y i j) σ) * Matrix.of (b' σ) :
          Matrix (Fin r) (Fin r) ℂ) = Function.update x τ (fun i j => (y * b) i j) σ
        rw [hbσ σ hσ, Function.update_of_ne hσ, Function.update_of_ne hσ]
        exact Matrix.mul_one _
    have hbc : bchar la b' = ∏ i, b i i ^ la τ i := by
      unfold bchar
      rw [Finset.prod_eq_single τ]
      · rw [hbτ]
      · intro σ _ hσ
        rw [hbσ σ hσ]
        exact Finset.prod_eq_one fun i _ => by simp
      · intro h'; exact absurd (Finset.mem_univ τ) h'
    have hmem : Function.update x τ (fun i j => y i j) ∈ X.dom := (hupd _).2 hy
    have hP2 := hP.2.1 _ hmem b' hb'B
    rw [hrm, hbc] at hP2
    have hdb : b.det = ∏ i, b i i := Matrix.det_of_upperTriangular hbt
    have hbii : ∀ i, b i i ≠ 0 := by
      intro i
      rw [hdb] at hb
      exact Finset.prod_ne_zero_iff.mp hb i (Finset.mem_univ i)
    have hchar : (∏ i, b i i ^ la τ i) * b.det ^ N = ReciprocityTheory.MultiplicativeHeights.triChar a b := by
      rw [hdb, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      unfold ReciprocityTheory.MultiplicativeHeights.triChar
      refine Finset.prod_congr rfl fun i _ => ?_
      have e : ((la τ i + N).toNat : ℤ) = la τ i + N := Int.toNat_of_nonneg (hN τ i)
      rw [← zpow_natCast (b i i) N, ← zpow_add₀ (hbii i), ← zpow_natCast, e]
    show P (Function.update x τ (fun i j => (y * b) i j)) * (y * b).det ^ N =
      ReciprocityTheory.MultiplicativeHeights.triChar a b * (P (Function.update x τ (fun i j => y i j)) * y.det ^ N)
    rw [hP2, Matrix.det_mul, mul_pow, ← hchar]
    ring
  obtain ⟨F, hF, hFe⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.bwPoly r a h hholo htri
  refine ⟨F, hF, fun y hy => ?_⟩
  have e := hFe (Matrix.of y) hy
  have e' : P (Function.update x τ y) * (Matrix.of y).det ^ N =
      MvPolynomial.eval (fun ij => y ij.1 ij.2) F := e
  rw [← e', inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hy), mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafMapMonoEpiIso
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.FreeMonoEpi

theorem freeP_map_mono (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) [Mono f] : Mono ((freeP R).map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [ModuleCat.mono_iff_injective]
  have hf : Function.Injective (f.app U) := (mono_iff_injective (f.app U)).1 inferInstance
  have hu : Function.Injective (uliftFunctor.{1}.map (f.app U)) := by
    intro a b h; cases a; cases b; exact congrArg ULift.up (hf (congrArg ULift.down h))
  exact Finsupp.mapDomain_injective hu

theorem free_map_mono (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) [Mono f] : Mono ((free R).map f) := by
  haveI := freeP_map_mono R f
  exact (presheafToSheaf _ _).map_mono ((freeP R).map f)

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (k ≫ g) a = Sec.res k (Sec.res g a) := by
  simp [Sec.res]

theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.map φ (Sec.res g a) = Sec.res g (Sec.map φ a) := by
  have := congrArg (fun h => ModuleCat.Hom.hom h a) (φ.hom.naturality g.op)
  simpa [Sec.map, Sec.res] using this

abbrev gsum (R : Type) [CommRing R] (P : PSh) (V : Scheme.{0}) (c : P.obj (op V) →₀ ULift.{1} R) : Sec ((free R).obj P) V :=
  c.sum fun x r => r • freeGen R P V x

theorem res_gsum (R : Type) [CommRing R] (P : PSh) {W V : Scheme.{0}} (k : W ⟶ V) (c : P.obj (op V) →₀ ULift.{1} R) :
    Sec.res k (gsum R P V c) = c.sum fun x r => r • freeGen R P W (P.map k.op x) := by
  simp only [gsum, Sec.res, map_finsuppSum, map_smul]
  refine Finsupp.sum_congr fun x _ => ?_
  congr 1
  exact (GlobalTheory.T.free_sections_ext_res_map R P ((free R).obj P)).2.2.1 W V k x

theorem res_gsum' (R : Type) [CommRing R] (P : PSh) {W V : Scheme.{0}} (k : W ⟶ V) (c : P.obj (op V) →₀ ULift.{1} R) :
    Sec.res k (gsum R P V c) = gsum R P W (Finsupp.mapDomain (P.map k.op) c) := by
  rw [res_gsum, gsum, Finsupp.sum_mapDomain_index (h := fun (x : P.obj (op W)) (r : ULift.{1} R) => r • freeGen R P W x)
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]

theorem map_gsum (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) {V : Scheme.{0}} (c : P.obj (op V) →₀ ULift.{1} R) :
    Sec.map ((free R).map f) (gsum R P V c) = gsum R Q V (Finsupp.mapDomain (f.app (op V)) c) := by
  rw [gsum, gsum, Finsupp.sum_mapDomain_index (h := fun (x : Q.obj (op V)) (r : ULift.{1} R) => r • freeGen R Q V x)
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp only [Sec.map, map_finsuppSum, map_smul]
  refine Finsupp.sum_congr fun x _ => ?_
  congr 1
  exact (GlobalTheory.T.free_sections_ext_res_map R P ((free R).obj P)).2.2.2 Q f V x

theorem loc_all {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.1 U P h

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (hPQ : ∀ V g, P V g → Q V g) :
    Loc U Q :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U P Q h hPQ

theorem loc_trans {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.1 U P h

theorem loc_fin {U : Scheme.{0}} {ι : Type} [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) : Loc U fun V g => ∀ i, P i V g :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.2.1 U ι P h

theorem free_map_epi (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q)
    (hs : ∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, f.app (op V) x = Q.map g.op y) : Epi ((free R).map f) := by
  rw [(GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections R ((free R).map f)).2.2.1]
  intro U b
  apply loc_trans
  refine loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R Q U).1 b) ?_
  rintro V g ⟨c, hc⟩
  have hl : Loc V fun W k => ∀ i : c.support, ∃ x, f.app (op W) x = Q.map k.op i.1 :=
    loc_fin (fun i : c.support => fun W k => ∃ x, f.app (op W) x = Q.map k.op i.1) (fun i => hs V i.1)
  refine loc_mono hl ?_
  intro W k hk
  choose x hx using hk
  refine ⟨∑ i : c.support, c i.1 • freeGen R P W (x i), ?_⟩
  have e1 : Sec.map ((free R).map f) (∑ i : c.support, c i.1 • freeGen R P W (x i)) =
      ∑ i : c.support, c i.1 • freeGen R Q W (Q.map k.op i.1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Sec.map, map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← hx i]; exact (GlobalTheory.T.free_sections_ext_res_map R P ((free R).obj P)).2.2.2 Q f W (x i)
  rw [e1, res_comp, hc, res_gsum, Finsupp.sum]
  exact Finset.sum_coe_sort c.support (fun y => c y • freeGen R Q W (Q.map k.op y))

theorem loc_kill {R : Type} [CommRing R] {P Q : PSh} (f : P ⟶ Q)
    (hi : ∀ U (x x' : P.obj (op U)), f.app (op U) x = f.app (op U) x' → Loc U fun _ g => P.map g.op x = P.map g.op x')
    {W : Scheme.{0}} (d : P.obj (op W) →₀ ULift.{1} R) (hd : Finsupp.mapDomain (f.app (op W)) d = 0) :
    Loc W fun _ k => Finsupp.mapDomain (P.map k.op) d = 0 := by
  classical
  have hl : Loc W fun W' k => ∀ i : d.support × d.support,
      f.app (op W) i.1.1 = f.app (op W) i.2.1 → P.map k.op i.1.1 = P.map k.op i.2.1 :=
    loc_fin _ fun i => by
      by_cases h : f.app (op W) i.1.1 = f.app (op W) i.2.1
      · exact loc_mono (hi W _ _ h) fun _ _ e _ => e
      · exact loc_all fun _ _ e => absurd e h
  refine loc_mono hl ?_
  intro W' k hk
  rcases d.support.eq_empty_or_nonempty with h0 | ⟨x0, _⟩
  · rw [Finsupp.support_eq_empty.1 h0, Finsupp.mapDomain_zero]
  let h : Q.obj (op W) → P.obj (op W') := fun y =>
    if hy : ∃ x ∈ d.support, f.app (op W) x = y then P.map k.op hy.choose else P.map k.op x0
  have e : Finsupp.mapDomain (P.map k.op) d = Finsupp.mapDomain (h ∘ f.app (op W)) d := by
    apply Finsupp.mapDomain_congr
    intro x hx
    have hy : ∃ x' ∈ d.support, f.app (op W) x' = f.app (op W) x := ⟨x, hx, rfl⟩
    show _ = h (f.app (op W) x)
    simp only [h, dif_pos hy]
    exact hk (⟨x, hx⟩, ⟨hy.choose, hy.choose_spec.1⟩) hy.choose_spec.2.symm
  rw [e, Finsupp.mapDomain_comp, hd, Finsupp.mapDomain_zero]

theorem free_map_mono_of_loc (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q)
    (hi : ∀ U (x x' : P.obj (op U)), f.app (op U) x = f.app (op U) x' → Loc U fun _ g => P.map g.op x = P.map g.op x') :
    Mono ((free R).map f) := by
  rw [(GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections R ((free R).map f)).2.1]
  intro U a ha
  apply loc_trans
  refine loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R P U).1 a) ?_
  rintro V g ⟨c, hc⟩
  have h0 : gsum R Q V (Finsupp.mapDomain (f.app (op V)) c) = 0 := by
    rw [← map_gsum, show gsum R P V c = Sec.res g a from hc.symm, map_res, ha]; simp [Sec.res]
  apply loc_trans
  refine loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R Q V).2 _ h0) ?_
  intro W k hk
  have hd : Finsupp.mapDomain (f.app (op W)) (Finsupp.mapDomain (P.map k.op) c) = 0 := by
    rw [← Finsupp.mapDomain_comp]
    rw [show (f.app (op W) ∘ P.map k.op) = (Q.map k.op ∘ f.app (op V)) from
      funext fun x => NatTrans.naturality_apply f k.op x]
    rw [Finsupp.mapDomain_comp]; exact hk
  refine loc_mono (loc_kill f hi _ hd) ?_
  intro W' k' hk'
  rw [res_comp, res_comp, hc, res_gsum', res_gsum', hk']
  simp [gsum]

end GlobalTheory.EtC.FreeMonoEpi

namespace GlobalTheory.EtC


open GlobalTheory.EtC.FreeMonoEpi in
theorem free_map_mono_epi_iso : ∀ (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q), (Mono f → Mono ((free R).map f)) ∧ ((∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, f.app (op V) x = Q.map g.op y) → Epi ((free R).map f)) ∧ ((∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, f.app (op V) x = Q.map g.op y) → (∀ U (x x' : P.obj (op U)), f.app (op U) x = f.app (op U) x' → Loc U fun _ g => P.map g.op x = P.map g.op x') → IsIso ((free R).map f)) := by
  intro R _ P Q f
  refine ⟨fun _ => free_map_mono R f, free_map_epi R f, fun hs hi => ?_⟩
  haveI := free_map_epi R f hs
  haveI := free_map_mono_of_loc R f hi
  exact isIso_of_mono_of_epi _

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCorrectionNextLevel
section
open MvPolynomial

namespace GlobalTheory.UnifCorr

variable {R : Type} [CommRing R] {σ : Type}

theorem coeff_X_pow_mul_mem (I : Ideal R) (i : σ) (k : ℕ) (G : MvPolynomial σ R)
    (h : ∀ m, AddMonoidAlgebra.coeff G m ∈ I) : ∀ m, AddMonoidAlgebra.coeff ((X i : MvPolynomial σ R) ^ k * G) m ∈ I := by
  intro m
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  split_ifs
  · exact I.mul_mem_left _ (h _)
  · exact I.zero_mem

theorem mem_of_coeff_mem (I : Ideal R) (K : Ideal (MvPolynomial σ R))
    (hC : ∀ a ∈ I, C a ∈ K) (G : MvPolynomial σ R) (h : ∀ m, AddMonoidAlgebra.coeff G m ∈ I) : G ∈ K := by
  rw [G.as_sum]
  refine K.sum_mem fun v _ => ?_
  rw [← mul_one (AddMonoidAlgebra.coeff G v), ← C_mul_monomial]
  exact K.mul_mem_right _ (hC _ (h v))

end GlobalTheory.UnifCorr

open GlobalTheory.UnifCorr in
theorem GlobalTheory.homogeneous_correction_next_level : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (n : ℕ) (K : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ i, ∃ N : ℕ, (X i : MvPolynomial (Fin (n + 1)) R) ^ N * F ∈ K e) → F ∈ K e) → (∀ e, ∀ a ∈ I ^ (e + 1), C a ∈ K e) → (∀ (e t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ K e → ∀ i, ∃ (N : ℕ) (G : MvPolynomial (Fin (n + 1)) R), G.IsHomogeneous (t + N) ∧ (∀ m, AddMonoidAlgebra.coeff G m ∈ I ^ (e + 1)) ∧ (X i : MvPolynomial (Fin (n + 1)) R) ^ N * F - G ∈ K (e + 1)) → ∃ t₀ : ℕ, ∀ t, t₀ ≤ t → ∀ (e : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ K e → ∃ G : MvPolynomial (Fin (n + 1)) R, G.IsHomogeneous t ∧ (∀ m, AddMonoidAlgebra.coeff G m ∈ I ^ (e + 1)) ∧ F - G ∈ K (e + 1) := by
  intro R _ _ I n K hsat hC hstep
  have hcoef : ∀ e (G : MvPolynomial (Fin (n + 1)) R), (∀ m, AddMonoidAlgebra.coeff G m ∈ I ^ (e + 1)) → G ∈ K e :=
    fun e G h => mem_of_coeff_mem (I ^ (e + 1)) (K e) (hC e) G h
  have hJ : ∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t →
      (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ K e → C a * F ∈ K (e + 1) := by
    intro e t a F ha hF _ hFK
    have hCF : (C a * F).IsHomogeneous t := by
      have := (isHomogeneous_C (Fin (n + 1)) a).mul hF
      rwa [zero_add] at this
    apply hsat (e + 1) t (C a * F) hCF
    intro i
    obtain ⟨N, G, _, hGc, hk⟩ := hstep e t F hF hFK i
    refine ⟨N, ?_⟩
    have h1 : C a * G ∈ K (e + 1) := by
      apply hcoef (e + 1)
      intro m
      rw [coeff_C_mul]
      have := Ideal.mul_mem_mul ha (hGc m)
      rwa [← pow_succ'] at this
    have : (X i : MvPolynomial (Fin (n + 1)) R) ^ N * (C a * F) = C a * (X i ^ N * F - G) + C a * G := by ring
    rw [this]
    exact add_mem ((K (e + 1)).mul_mem_left _ hk) h1
  obtain ⟨d₀, hd₀⟩ := _root_.GlobalTheory.uniform_serre_sections R I n K hJ
  refine ⟨d₀, fun t ht e F hF hFK => ?_⟩
  choose N G hG hGc hk using hstep e t F hF hFK
  obtain ⟨M, hNM⟩ : ∃ M, ∀ i, N i ≤ M :=
    ⟨∑ i, N i, fun i => Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)⟩
  let G' : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R := fun i => X i ^ (M - N i) * G i
  have hXM : ∀ i, (X i : MvPolynomial (Fin (n + 1)) R) ^ M = X i ^ (M - N i) * X i ^ N i := fun i => by
    rw [← pow_add, Nat.sub_add_cancel (hNM i)]
  have hG'h : ∀ i, (G' i).IsHomogeneous (t + M) := fun i => by
    show (X i ^ (M - N i) * G i).IsHomogeneous (t + M)
    rw [show t + M = (M - N i) + (t + N i) by have := hNM i; omega]
    exact (isHomogeneous_X_pow i (M - N i)).mul (hG i)
  have hG'c : ∀ i m, AddMonoidAlgebra.coeff (G' i) m ∈ I ^ (e + 1) := fun i => coeff_X_pow_mul_mem _ i _ _ (hGc i)
  have hk' : ∀ i, (X i : MvPolynomial (Fin (n + 1)) R) ^ M * F - G' i ∈ K (e + 1) := fun i => by
    have : (X i : MvPolynomial (Fin (n + 1)) R) ^ M * F - G' i = X i ^ (M - N i) * (X i ^ N i * F - G i) := by
      simp only [G', hXM i]; ring
    rw [this]; exact (K (e + 1)).mul_mem_left _ (hk i)
  obtain ⟨G0, hG0, hG0c, hL⟩ := hd₀ t ht (e + 1) M G' hG'h hG'c (fun i j => ⟨0, by
    have : ((X i : MvPolynomial (Fin (n + 1)) R) * X j) ^ 0 * (X j ^ M * G' i - X i ^ M * G' j)
        = X i ^ M * (X j ^ M * F - G' j) - X j ^ M * (X i ^ M * F - G' i) := by ring
    rw [this]
    exact sub_mem ((K (e + 1)).mul_mem_left _ (hk' j)) ((K (e + 1)).mul_mem_left _ (hk' i))⟩)
  refine ⟨G0, hG0, hG0c, ?_⟩
  apply hsat (e + 1) t (F - G0) (hF.sub hG0)
  intro i
  obtain ⟨L, hLi⟩ := hL i
  refine ⟨L + M, ?_⟩
  have : (X i : MvPolynomial (Fin (n + 1)) R) ^ (L + M) * (F - G0)
      = X i ^ L * (X i ^ M * F - G' i) + X i ^ L * (G' i - X i ^ M * G0) := by ring
  rw [this]
  exact add_mem ((K (e + 1)).mul_mem_left _ (hk' i)) hLi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldMonicRootsTensorFractionRingStrictlyHenseStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isField_monicRoots_tensor_fractionRing_strictlyHenselian : ∀ (A O : Type) [CommRing A] [IsDomain A] [CommRing O] [Algebra A O], AIC A → SH O → IndEt A O → IsField (O ⊗[A] FractionRing A) ∧ AIC (O ⊗[A] FractionRing A) := by
  first | (exact @GlobalTheory.isField_aic_tensor_fractionRing_of_strictlyHenselian) | (exact GlobalTheory.isField_aic_tensor_fractionRing_of_strictlyHenselian) | (intros; apply GlobalTheory.isField_aic_tensor_fractionRing_of_strictlyHenselian  <;> assumption)
end

