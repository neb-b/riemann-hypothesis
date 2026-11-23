module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0089
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.LinearIndependentSumElimOfExact
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0087
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0065
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermJetUnitOnChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

section Ring

variable {k : Type} [Field k] {d : ℕ}

theorem homAt_comp_homAt {X : Scheme.{0}} (x : Sp k ⟶ X) {A B C : Type} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] [CommRing C] [Algebra k C] (f : A →ₐ[k] B) (h : B →ₐ[k] C) :
    homAt x h ≫ homAt x f = homAt x (h.comp f) := by
  apply Over.OverMorphism.ext
  simp only [homAt, Over.comp_left, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem jetAug_comp_copy (n M : ℕ) (i : Fin n) :
    (jetAug : Jet k (Fin n × Fin d) M →ₐ[k] k).comp (jetCopy d M i) = jetAug := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro q
  have e : jetCopy (S := k) d M i (Ideal.Quotient.mk _ (MvPolynomial.X q)) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, q.2)) :=
    congrArg (Ideal.Quotient.mk _) (MvPolynomial.aeval_X _ q)
  have a₁ : (jetAug : Jet k (Fin n × Fin d) M →ₐ[k] k) (Ideal.Quotient.mk _ (MvPolynomial.X (i, q.2))) = 0 :=
    MvPolynomial.aeval_X _ _
  have a₂ : (jetAug : Jet k (Fin 1 × Fin d) M →ₐ[k] k) (Ideal.Quotient.mk _ (MvPolynomial.X q)) = 0 :=
    MvPolynomial.aeval_X _ _
  show (jetAug : Jet k (Fin n × Fin d) M →ₐ[k] k) (jetCopy (S := k) d M i (Ideal.Quotient.mk _ (MvPolynomial.X q))) =
    (jetAug : Jet k (Fin 1 × Fin d) M →ₐ[k] k) (Ideal.Quotient.mk _ (MvPolynomial.X q))
  rw [e, a₁, a₂]

def sub₀ (M : ℕ) : Jet k (Fin 2 × Fin d) M →ₐ[k] Jet k (Fin 1 × Fin d) M :=
  jetSubstP M fun p : Fin 2 × Fin d =>
    (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k) p.1 p.2

def trJ (m M : ℕ) (h : m ≤ M) : Jet k (Fin 1 × Fin d) M →ₐ[k] Jet k (Fin 1 × Fin d) m :=
  Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (by omega))

theorem aug_jq (w : Fin d → k) (p m : ℕ) :
    ((jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m) :
        Jet (Jet k (Fin 1 × Fin d) m) Unit p →+* Jet k (Fin 1 × Fin d) m).comp
      ((jq w p m : _ →ₐ[k] _) : Jet k (Fin 2 × Fin d) (p + m + 1) →+* Jet (Jet k (Fin 1 × Fin d) m) Unit p) =
    ((trJ m (p + m + 1) (by omega)).comp (sub₀ (p + m + 1)) :
      Jet k (Fin 2 × Fin d) (p + m + 1) →ₐ[k] Jet k (Fin 1 × Fin d) m).toRingHom := by
  have key : ((jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m).restrictScalars k).comp
      (jq w p m) = (trJ m (p + m + 1) (by omega)).comp (sub₀ (p + m + 1)) := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    have hq : jq w p m (Ideal.Quotient.mk _ (MvPolynomial.X (i, j))) =
        if i = 0 then algebraMap k _ (w j) * dQ (Jet k (Fin 1 × Fin d) m) p
        else inR (k := k) (Jet k (Fin 1 × Fin d) m) p (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) :=
      MvPolynomial.aeval_X _ _
    have hs : sub₀ (k := k) (d := d) (p + m + 1) (Ideal.Quotient.mk _ (MvPolynomial.X (i, j))) =
        Ideal.Quotient.mk _ ((![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k) i j - MvPolynomial.C (MvPolynomial.constantCoeff
            ((![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] :
              Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k) i j))) :=
      congrArg (Ideal.Quotient.mk _) (MvPolynomial.aeval_X _ _)
    have hd : (jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m)
        (dQ (Jet k (Fin 1 × Fin d) m) p) = 0 := MvPolynomial.aeval_X _ _
    show (jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m)
        (jq w p m (Ideal.Quotient.mk _ (MvPolynomial.X (i, j)))) =
      trJ m (p + m + 1) (by omega) (sub₀ (p + m + 1) (Ideal.Quotient.mk _ (MvPolynomial.X (i, j))))
    rw [hq, hs]
    fin_cases i
    · simp only [Fin.zero_eta, if_true, map_mul, hd, mul_zero]
      simp [trJ]
    · simp [trJ, inR]
  exact congrArg AlgHom.toRingHom key

end Ring

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

theorem comp_psum_one {T T' : Over X0} (U : T' ⟶ T) {n : ℕ} (xs : Fin n → (T ⟶ t.G)) (h : ∀ i, U ≫ xs i = 1)
    (I : Finset (Fin n)) : U ≫ psum t.G xs I = 1 := by
  have e := psum_hom (preHom (G := t.G) U) xs I
  have e' : (fun i => preHom (G := t.G) U (xs i)) = fun _ => (1 : T' ⟶ t.G) := funext h
  rw [e'] at e
  refine e.trans ?_
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => rfl
  | cons a l ih => exact (congrArg ((1 : T' ⟶ t.G) * ·) ih).trans (_root_.one_mul _)

end Pts


set_option maxHeartbeats 1000000 in
theorem frame_test_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ) (j₀ : t.PP.L.ι), ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ → ∃ e₀ : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ, (jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m) e₀ = 1 ∧ ∀ (z : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p)) (J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → (∀ ψ : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀) → val (g.e (p + m + 1)) (homAt x (jq w p m)).left z J = gm (𝟙 _) z ⊤ (unitΓ e₀) := by
  intro E _ _ _ H _ X0 t k _ p x d g w m j₀ hj₀
  have hpt : ∀ (I : ULift.{0} (Finset (Fin 2))) q, ((homAt x (jq w p m)).left ≫
      cφG t ![jptG t x d g.x (p + m + 1) (0 : Fin 2), jptG t x d g.x (p + m + 1) (1 : Fin 2)] I) q ∈ t.PP.L.U j₀ := by
    intro I q
    have h0 : ∀ i : Fin 2, homAt x (jetAug : Jet k (Fin 2 × Fin d) (p + m + 1) →ₐ[k] k) ≫
        jptG t x d g.x (p + m + 1) i = 1 := by
      intro i
      rw [jptG, ← Category.assoc, homAt_comp_homAt, jetAug_comp_copy]
      exact g.chart.zero _
    have hz := comp_psum_one t (homAt x (jetAug : Jet k (Fin 2 × Fin d) (p + m + 1) →ₐ[k] k))
      ![jptG t x d g.x (p + m + 1) (0 : Fin 2), jptG t x d g.x (p + m + 1) (1 : Fin 2)]
      (by intro i; fin_cases i; exacts [h0 0, h0 1]) I.down
    rw [Scheme.Hom.comp_apply]
    exact jet_left_mem t x j₀ hj₀ _ hz _
  have hred : ∀ (z' : Sp (Jet k (Fin 1 × Fin d) m)) (J' : (Sp (Jet k (Fin 1 × Fin d) m) ⟶ t.G.left) → t.PP.L.ι),
      Good t.PP.L z' J' → val (g.e (p + m + 1))
        (spMap ((jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m) :
          Jet (Jet k (Fin 1 × Fin d) m) Unit p →+* Jet k (Fin 1 × Fin d) m) ≫ (homAt x (jq w p m)).left) z' J' = 1 := by
    intro z' J' hJ'
    have e : spMap ((jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m) :
          Jet (Jet k (Fin 1 × Fin d) m) Unit p →+* Jet k (Fin 1 × Fin d) m) ≫ (homAt x (jq w p m)).left =
        spMap ((trJ m (p + m + 1) (by omega) : Jet k (Fin 1 × Fin d) (p + m + 1) →ₐ[k] _) :
          Jet k (Fin 1 × Fin d) (p + m + 1) →+* Jet k (Fin 1 × Fin d) m) ≫ (homAt x (sub₀ (p + m + 1))).left := by
      have := aug_jq w p m
      simp only [homAt, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [this]
      rfl
    rw [e, ← val_pull hJ' (g.e (p + m + 1)) (homAt x (sub₀ (p + m + 1))).left]
    exact (val_corr hJ' (g.axes (p + m + 1)).1 _).trans (val_one _)
  have exists_unitΓ_eq {A : Type} [CommRing A] (u : Γ(Sp A, ⊤)ˣ) : ∃ e : Aˣ, unitΓ e = u := by
    refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom u, Units.ext ?_⟩
    exact congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id

  have val_eq_unit_of_red : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (B : Type) [CommRing B] (p : ℕ) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp (Jet B Unit p) ⟶ Y) (j₀ : L.ι), (∀ κ q, (r ≫ φ κ) q ∈ L.U j₀) → (∀ (z' : Sp B) (J' : (Sp B ⟶ X) → L.ι), Good L z' J' → (∀ κ, J' (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫ r ≫ φ κ) = j₀) → val t (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫ r) z' J' = 1) → ∃ e₀ : (Jet B Unit p)ˣ, (jetAug : Jet B Unit p →ₐ[B] B) e₀ = 1 ∧ ∀ (z : Sp (Jet B Unit p)) (J : (Sp (Jet B Unit p) ⟶ X) → L.ι), Good L z J → (∀ κ, J (r ≫ φ κ) = j₀) → val t r z J = gm (𝟙 _) z ⊤ (unitΓ e₀) := by
    intro X Y L hL B _ p K _ φ ε t r j₀ h₁ h₂
    have hW : (⊤ : (Sp (Jet B Unit p)).Opens) ≤ r ⁻¹ᵁ LB.wchart L φ (fun _ => j₀) :=
      fun q _ => Set.mem_iInter.2 fun κ => h₁ κ q
    obtain ⟨e₀, he₀⟩ := exists_unitΓ_eq (res hW (pullU r _ (t.s fun _ => j₀)))
    have key : ∀ (Z : Scheme.{0}) (f : Z ⟶ Sp (Jet B Unit p)) (z : Z),
        gm f z ⊤ (unitΓ e₀) = gm (f ≫ r) z (LB.wchart L φ (fun _ => j₀)) (t.s fun _ => j₀) := by
      intro Z f z
      rw [he₀, gm_res f z hW (Set.mem_univ _)]
      exact gm_pull f r z _ (hW (Set.mem_univ _)) _
    refine ⟨e₀, ?_, ?_⟩
    · have hv : pullU (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B)) ⊤ (unitΓ e₀) = 1 := by
        apply unit_ext
        intro z' _
        obtain ⟨J', hJ', e⟩ := exists_good L hL z'
          (fun κ => spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫ r ≫ φ κ) (fun _ => j₀)
          (fun _ _ _ => rfl) (fun κ => h₁ κ _)
        have hv := h₂ z' J' hJ' e
        rw [val_of t _ z' J' (fun _ => j₀) (fun κ => by rw [Category.assoc]; exact e κ), ← key] at hv
        have hp := gm_pull (𝟙 _) (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B)) z' ⊤ (Set.mem_univ _)
          (unitΓ e₀)
        rw [Category.id_comp] at hp
        rw [map_one]
        exact hp.trans hv
      apply toΓ_inj
      rw [map_one]
      exact (spMap_toΓ _ _).symm.trans (congrArg Units.val hv)
    · intro z J _ hc
      rw [val_of t r z J (fun _ => j₀) hc, key, Category.id_comp]
  obtain ⟨e₀, he, hv⟩ := val_eq_unit_of_red t.G.left (Sp (Jet k (Fin 2 × Fin d) (p + m + 1))) t.PP.L t.PP.isLB
    (Jet k (Fin 1 × Fin d) m) p (ULift (Finset (Fin 2)))
    (cφG t ![jptG t x d g.x (p + m + 1) (0 : Fin 2), jptG t x d g.x (p + m + 1) (1 : Fin 2)]) (cε 2) (g.e (p + m + 1))
    (homAt x (jq w p m)).left j₀ hpt (fun z' J' hJ' _ => hred z' J' hJ')
  exact ⟨e₀, he, fun z J hJ hc => hv z J hJ fun I => hc _ (hpt I z)⟩

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GradedDegreeFormula
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GrLine

open GroundTheory.Heights₂.Heights

section Algebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem linearIndependent_snoc {F : Submodule R M}
    (hsat : ∀ (a : R) (x : M), a ≠ 0 → a • x ∈ F → x ∈ F) {n : ℕ} {f : Fin n → M}
    (hf : ∀ a, f a ∈ F) (hli : LinearIndependent R f) {s : M} (hs : s ∉ F) :
    LinearIndependent R (Fin.snoc f s : Fin (n + 1) → M) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_castSucc] at hg
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at hg
  have hlast : g (Fin.last n) = 0 := by
    by_contra h0
    apply hs
    apply hsat _ _ h0
    have : g (Fin.last n) • s = -∑ a : Fin n, g a.castSucc • f a := eq_neg_of_add_eq_zero_right hg
    rw [this]
    exact F.neg_mem (F.sum_mem fun a _ => F.smul_mem _ (hf a))
  rw [hlast, zero_smul, add_zero] at hg
  have hz := Fintype.linearIndependent_iff.mp hli (fun a => g a.castSucc) hg
  intro j
  exact Fin.lastCases hlast (fun a => hz a) j

theorem card_quotient_line {F G P : Submodule R M} (hFG : F ≤ G) (hPF : P ≤ F)
    (hsat : ∀ (a : R) (x : M), a ≠ 0 → a • x ∈ F → x ∈ F) {s : M} (hs : s ∉ F)
    (T : Submodule R G) (U : Submodule R F)
    (hT : ∀ x : G, x ∈ T ↔ (x : M) ∈ P ⊔ Submodule.span R {s})
    (hU : ∀ x : F, x ∈ U ↔ (x : M) ∈ P) :
    Nat.card (G ⧸ T) =
      Nat.card (G ⧸ (F ⊔ Submodule.span R {s}).comap G.subtype) * Nat.card (F ⧸ U) := by
  set S : Submodule R G := (F ⊔ Submodule.span R {s}).comap G.subtype with hS
  have hTS : T ≤ S := fun x hx => (sup_le_sup_right hPF _) ((hT x).1 hx)
  let φ : F →ₗ[R] G ⧸ T := T.mkQ ∘ₗ Submodule.inclusion hFG
  have hker : LinearMap.ker φ = U := by
    ext x
    rw [hU]
    simp only [φ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    rw [hT]
    change (x : M) ∈ P ⊔ Submodule.span R {s} ↔ _
    constructor
    · intro h
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
      have ha : a = 0 := by
        by_contra h0
        apply hs
        apply hsat a s h0
        have : a • s = (x : M) - y := by rw [← hyz]; abel
        rw [this]
        exact F.sub_mem x.2 (hPF hy)
      rw [ha, zero_smul, add_zero] at hyz
      rwa [← hyz]
    · exact fun h => Submodule.mem_sup_left h
  have hrange : LinearMap.range φ = S.map T.mkQ := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Submodule.inclusion hFG x, Submodule.mem_sup_left x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, hx, z, hz, hxz⟩ := Submodule.mem_sup.1 (show (y : M) ∈ F ⊔ Submodule.span R {s} from hy)
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
      refine ⟨⟨x, hx⟩, ?_⟩
      simp only [φ, LinearMap.comp_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq, hT]
      have : ((Submodule.inclusion hFG ⟨x, hx⟩ - y : G) : M) = -(a • s) := by
        change x - (y : M) = _
        rw [← hxz]
        abel
      rw [this]
      exact neg_mem (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self s)))
  have hc : Nat.card (F ⧸ U) = Nat.card (S.map T.mkQ) := by
    rw [← hker, ← hrange]
    exact Nat.card_congr φ.quotKerEquivRange.toEquiv
  rw [hc, mul_comm]
  exact (Submodule.card_quotient_mul_card_quotient S T hTS).symm

end Algebra


open scoped ComplexOrder in
theorem gramDet_re_eq_norm {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (σ : L →+* ℂ) {n : ℕ} {e : Fin n → B.carrier} (hli : LinearIndependent (𝓞 L) e) :
    GroundTheory.Heights₂.Heights.gramDet B.metric σ e = ‖B.gramDet σ e‖ := by
  have hd : B.gramDet σ e = (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det := rfl
  have hp : 0 < (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det :=
    (Matrix.posDef_gram_of_linearIndependent (linearIndependent_fibreVec B.metric σ hli)).det_pos
  obtain ⟨h1, h2⟩ := Complex.lt_def.mp hp
  have hz : (((Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det).re : ℂ) =
      (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det :=
    Complex.ext (by simp) (by simpa using h2)
  rw [hd, ← hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using h1)]
  rfl

theorem grDeg_eq : ∀ (L : Type) [Field L] [NumberField L] (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (r : ℕ) (A : SatFlag B r) (i : Fin r) (f : Fin i → B.carrier) (s : B.carrier), (∀ a, f a ∈ A.F i.castSucc) → LinearIndependent (𝓞 L) f → s ∈ A.F i.succ → s ∉ A.F i.castSucc → A.grDeg i = (Module.finrank ℚ L : ℝ)⁻¹ * (Real.log (Nat.card (A.F i.succ ⧸ (A.F i.castSucc ⊔ Submodule.span (𝓞 L) {s}).comap (A.F i.succ).subtype)) - (1 / 2) * ∑ σ : L →+* ℂ, (Real.log ‖B.gramDet σ (Fin.snoc f s : Fin (i + 1) → B.carrier)‖ - Real.log ‖B.gramDet σ f‖)) := by
  intro L _ _ B r A i f s hf hli hs hs0
  have hFG : A.F i.castSucc ≤ A.F i.succ := A.mono (Fin.castSucc_lt_succ).le
  have hsat : ∀ (a : 𝓞 L) (x : B.carrier), a ≠ 0 → a • x ∈ A.F i.castSucc → x ∈ A.F i.castSucc :=
    A.sat i.castSucc
  have hsn : LinearIndependent (𝓞 L) (Fin.snoc f s : Fin (i + 1) → B.carrier) :=
    linearIndependent_snoc hsat hf hli hs0
  have hmem : ∀ a, (Fin.snoc f s : Fin (i + 1) → B.carrier) a ∈ A.F i.succ := by
    intro a
    refine Fin.lastCases ?_ (fun j => ?_) a
    · simpa using hs
    · simpa using hFG (hf j)
  let f' : Fin i → A.F i.castSucc := fun a => ⟨f a, hf a⟩
  let g' : Fin (i + 1) → A.F i.succ := fun a => ⟨(Fin.snoc f s : Fin (i + 1) → B.carrier) a, hmem a⟩
  have hf' : LinearIndependent (𝓞 L) f' := LinearIndependent.of_comp (A.F i.castSucc).subtype hli
  have hg' : LinearIndependent (𝓞 L) g' := LinearIndependent.of_comp (A.F i.succ).subtype hsn
  have hcF : Fintype.card (Fin i) = B.rank (A.F i.castSucc) := by
    rw [Fintype.card_fin, A.rank]; simp
  have hcG : Fintype.card (Fin (i + 1)) = B.rank (A.F i.succ) := by
    rw [Fintype.card_fin, A.rank]; simp
  have hP : Submodule.span (𝓞 L) (Set.range f) ≤ A.F i.castSucc :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hf a)
  have hU : ∀ x : A.F i.castSucc, x ∈ Submodule.span (𝓞 L) (Set.range f') ↔
      (x : B.carrier) ∈ Submodule.span (𝓞 L) (Set.range f) := by
    intro x
    have hm : (Submodule.span (𝓞 L) (Set.range f')).map (A.F i.castSucc).subtype =
        Submodule.span (𝓞 L) (Set.range f) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [← hm]
    constructor
    · exact fun h => ⟨x, h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
  have hT : ∀ x : A.F i.succ, x ∈ Submodule.span (𝓞 L) (Set.range g') ↔
      (x : B.carrier) ∈ Submodule.span (𝓞 L) (Set.range f) ⊔ Submodule.span (𝓞 L) {s} := by
    intro x
    have hm : (Submodule.span (𝓞 L) (Set.range g')).map (A.F i.succ).subtype =
        Submodule.span (𝓞 L) (Set.range f) ⊔ Submodule.span (𝓞 L) {s} := by
      rw [Submodule.map_span, ← Set.range_comp, ← Submodule.span_union]
      congr 1
      have hr : Set.range ((A.F i.succ).subtype ∘ g') =
          Set.range (Fin.snoc f s : Fin (i + 1) → B.carrier) := rfl
      rw [hr]
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        refine Fin.lastCases ?_ (fun j => ?_) a
        · right; simp
        · left; exact ⟨j, by simp⟩
      · rintro (⟨j, rfl⟩ | hy)
        · exact ⟨j.castSucc, by simp⟩
        · exact ⟨Fin.last _, by simpa using hy.symm⟩
    rw [← hm]
    constructor
    · exact fun h => ⟨x, h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
  have hidx := card_quotient_line hFG hP hsat hs0 _ _ hT hU
  have hfinF : Finite (A.F i.castSucc ⧸ Submodule.span (𝓞 L) (Set.range f')) :=
    finite_quotient_span hf' hcF
  have hfinG : Finite (A.F i.succ ⧸ Submodule.span (𝓞 L) (Set.range g')) :=
    finite_quotient_span hg' hcG
  have hne : (Nat.card (A.F i.succ ⧸ Submodule.span (𝓞 L) (Set.range g')) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hlog : Real.log (Nat.card (A.F i.succ ⧸ Submodule.span (𝓞 L) (Set.range g'))) =
      Real.log (Nat.card (A.F i.succ ⧸ (A.F i.castSucc ⊔ Submodule.span (𝓞 L) {s}).comap (A.F i.succ).subtype)) +
        Real.log (Nat.card (A.F i.castSucc ⧸ Submodule.span (𝓞 L) (Set.range f'))) := by
    rw [hidx] at hne ⊢
    push_cast at hne ⊢
    exact Real.log_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne)
  have hgF : ∀ σ : L →+* ℂ, GroundTheory.Heights₂.Heights.gramDet B.metric σ
      (fun a => ((f' a : A.F i.castSucc) : B.carrier)) = ‖B.gramDet σ f‖ :=
    fun σ => gramDet_re_eq_norm B σ hli
  have hgG : ∀ σ : L →+* ℂ, GroundTheory.Heights₂.Heights.gramDet B.metric σ
      (fun a => ((g' a : A.F i.succ) : B.carrier)) =
        ‖B.gramDet σ (Fin.snoc f s : Fin (i + 1) → B.carrier)‖ :=
    fun σ => gramDet_re_eq_norm B σ hsn
  rw [SatFlag.grDeg, HermitianBundle.normDegree, HermitianBundle.normDegree,
    B.degree_eq_of_linearIndependent _ hf' hcF, B.degree_eq_of_linearIndependent _ hg' hcG, hlog]
  simp only [hgF, hgG, Finset.sum_sub_distrib]
  ring

end GlobalTheory.CompanionTheory.Ar.GrLine
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyFlatHerm
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem FlatHerm.inter_eq : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω)
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d : ℕ),
    IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W →
    IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    I W (n + 1) (Fin.snoc L A) = S.ht * ptsIntegral W (pot L) (fun _ => 1) := by
  intro hP K _ ι _ Ω _ F _ _ y φ I W n L A S d hI hY hO hyW hW hL hA
  obtain ⟨u, hu, -⟩ := GlobalTheory.T.exists_place_weight_conj_invariant K ι Ω F y φ (fun σ => Real.log (S.κ σ)) hO
  rw [_root_.GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.inter_eq_neg_integral K ι Ω F y φ I W n L A S d u hI hY hO hyW hW hL hA hu,
    _root_.GlobalTheory.CompanionTheory.Ar.Flat.ptsIntegral_eq_mean hP K ι Ω F y φ I W n L d (fun σ => Real.log (S.κ σ)) u hI hY hO hyW hW hL
      (fun σ => congrArg Real.log (S.κ_conj σ)) (fun σ z hz => (hu.near σ z hz).self_of_nhds),
    FlatHerm.ht, neg_mul]

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSubFibreSubFib
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
  {Li : Type} [AddCommGroup Li] [Module Ω Li] {L : Type} [Field L] [NumberField L]

def subGens (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) : Set V :=
  {x' | ∃ e ∈ U, ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G,
    M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x').left)}

def subFib (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) : Submodule (𝓞 L) V where
  carrier := {x | ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ Submodule.span (𝓞 L) (subGens M U z MB)}
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
    · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  smul_mem' := by
    rintro c x ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem mem_subFib {M : LieModel G ξ Li} {U : Submodule Ω Li} {z : Sp (𝓞 L) ⟶ X} {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] {MB : LieModel G z V} {x : V} :
    x ∈ subFib M U z MB ↔ ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ Submodule.span (𝓞 L) (subGens M U z MB) := Iff.rfl

theorem isSubFibre_subFib (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) : IsSubFibre M U z MB (subFib M U z MB) := fun _ => Iff.rfl

theorem subFib_mono (M : LieModel G ξ Li) {U U' : Submodule Ω Li} (h : U ≤ U') (z : Sp (𝓞 L) ⟶ X) {V : Type}
    [AddCommGroup V] [Module (𝓞 L) V] (MB : LieModel G z V) : subFib M U z MB ≤ subFib M U' z MB := by
  rintro x ⟨a, ha, hx⟩
  refine ⟨a, ha, Submodule.span_mono ?_ hx⟩
  rintro y ⟨e, he, r⟩
  exact ⟨e, h he, r⟩

theorem subFib_saturated (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X)
    (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier) : B.Saturated (subFib M U z MB) := by
  rintro a x ha ⟨b, hb, hx⟩
  exact ⟨b * a, mul_ne_zero hb ha, by rwa [mul_smul]⟩

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleCocyclePullbackTransformStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_cocycle_pullback_transform : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (a b : Y ⟶ X), (∀ y, a y = b y) → ∀ (t : ∀ j, Γ(Y, b ⁻¹ᵁ L.U j)ˣ), (∀ (j j' : L.ι) (h : b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')), res (show b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ b ⁻¹ᵁ L.U j from fun _ hy => hy.1) (t j) = Units.map (a.appLE _ _ h).hom.toMonoidHom (L.g j j') * (pullU b _ (L.g j j'))⁻¹ * res (show b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ b ⁻¹ᵁ L.U j' from fun _ hy => hy.2) (t j')) → ∃ c : LB.Gen (LB.LinComb L (K := Fin 2) ![a, b] ![1, -1]), c.IsGen := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_of_units | exact GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_of_units | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_of_units <;> assumption)
end

