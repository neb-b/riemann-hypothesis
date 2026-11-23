module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPosLowerBoundNearMax
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AllClassesOccur
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

theorem GlobalTheory.all_classes_occur :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G G' : Matrix (Fin r) (Fin r) E), (∀ a b, FD.cc (G a b) = G b a) → (∀ a b, FD.cc (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ p0 : ℕ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G' Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ))) → (∃ z : E, G'.det = z * FD.cc z * G.det) → ∃ ga : GL (Fin r) E, ∀ x y, FD.herm G ((ga : Matrix (Fin r) (Fin r) E) *ᵥ x) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ y) = FD.herm G' x y) → (∀ (F : Type) [Field F] [NumberField F] (δ x : F), δ ≠ 0 → x ≠ 0 → (∀ σ : F →+* ℝ, ∃ a b : ℝ, σ x = a ^ 2 - σ δ * b ^ 2) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2) → ∃ a b : F, x = a ^ 2 - δ * b ^ 2) → Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty), l.A = 1 → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La), D'.p = D.p → D'.q = D.q → (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) → (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a') → ∃ (i : Fin U.n) (gam : D'.La ≃ₗ[𝓞 E] (U.Di i).La), (∀ a a', (U.Di i).EF (gam a) (gam a') = D'.EF a a') ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam (f l.M a) = U.t i a + l.M • e := by
  intro hL hN hLaw hQ E _ _ _ H D l Xo σ g ty U hA hσ hty D' f hp hq hf hE
  let i₀ : Fin U.n := ⟨0, U.n_pos⟩
  obtain ⟨hp₀, hq₀⟩ := U.sig i₀
  have hξ : FD.cc (H.rt : E) = -(H.rt : E) := by
    have h2 : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
      simpa using this
    have h3 : (FD.cc (H.rt : E)) ^ 2 = (H.rt : E) ^ 2 := by
      unfold FD.cc
      rw [← map_pow, h2, map_neg, map_natCast]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h3 with h | h
    · exfalso
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have h4 : starRingEnd ℂ (τ (H.rt : E)) = τ (H.rt : E) := by
        rw [← IsCMField.complexEmbedding_complexConj]
        exact congrArg τ h
      obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h4
      have h5 := congrArg τ h2
      rw [map_pow, hr, map_neg, map_natCast] at h5
      have h6 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h5
      have h7 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      nlinarith [sq_nonneg r]
    · exact h
  have hξ0 : (H.rt : E) ≠ 0 := by
    intro h
    have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
    simp only [h, RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_natCast] at this
    have h2 : (H.d : E) = 0 := by
      simpa using this
    exact H.d_prime.ne_zero (by exact_mod_cast h2)
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H (U.Di i₀) (H.rt : E) hξ hξ0 _ rfl
  obtain ⟨φ', hφ'⟩ := _root_.GlobalTheory.model_in_same_space hL hN E H (U.Di i₀) D' _ _ Gm φ (hp.trans hp₀.symm) (hq.trans hq₀.symm) hξ hφ
  obtain ⟨hg, P₀, hP₀⟩ := (_root_.GlobalTheory.PeriodExists.typeFn_period_exist E H (U.Di i₀)).2.1 g ty (by rw [hp₀, hq₀]; exact hty)
  rw [hp₀, hq₀] at hg
  obtain ⟨N, j, j', P', hj, hP', h₁, h₂⟩ :=
    GlobalTheory.datum_commensurable_period E H (U.Di i₀) D' _ _ Gm φ φ' g ty hξ hφ hφ' P₀ hP₀
  obtain ⟨t₀, e₀, -, -, ht₀⟩ := _root_.GlobalTheory.UnivFibre.exists_fibre_uniformised E H D l Xo σ g ty U i₀ P₀ hσ hg hP₀
  obtain ⟨t, e, ht⟩ := GlobalTheory.exists_uniformised_quotient_of_commensurable hLaw hQ E H (U.Di i₀) D' g ty P₀ P' N j j' t₀ e₀
    (hp.trans hp₀.symm) (hq.trans hq₀.symm) hj hP₀ hP' h₁ h₂ ht₀
  obtain ⟨o, m, hm⟩ := _root_.GlobalTheory.UnifObj.exists_obj_of_uniformised hLaw E H D D' l σ g ty P' t e f hA hσ hp hq hP' ht hf hE
  obtain ⟨y, ⟨hy, ⟨om⟩⟩, -⟩ := Xo.rep (Sp ℂ) (spMap σ) inferInstance o
  obtain ⟨i, P, hP, rfl⟩ := U.onto y hy
  obtain ⟨n, hn⟩ : ∃ n : SABMap t Xo.univ.t (U.u i P), n.φ = m.φ ≫ om.toSABMap.φ := by
    have := sabComp pullCubComp E H _ _ _ _ _ _ _ _ om.toSABMap m
    rwa [Category.id_comp] at this
  obtain ⟨h, gam, hh, hgam, hiso⟩ := _root_.GlobalTheory.familyUnif_fibre_lattice_match E H D l Xo σ g ty U i P D' P' t e n hP hP' ht
  refine ⟨i, gam, hiso, fun a ha => ?_⟩
  have hM : (l.M : ℂ) ≠ 0 := by
    have := l.three_le
    exact_mod_cast (by omega : l.M ≠ 0)
  have k₁ : U.ex i P ((l.M : ℂ)⁻¹ • P (gam (f l.M a))) = U.ex i P ((l.M : ℂ)⁻¹ • P (U.t i a)) := by
    apply Over.OverMorphism.ext
    rw [← U.ex_eta i P hP a ha, hgam, ← map_smul, ← hh, hn, ← Category.assoc, hm a ha, om.eta, Over.comp_left]
    congr 1
  have k₂ : U.ex i P ((l.M : ℂ)⁻¹ • P (gam (f l.M a)) - (l.M : ℂ)⁻¹ • P (U.t i a)) = 1 := by
    have := U.ex_add i P hP ((l.M : ℂ)⁻¹ • P (gam (f l.M a)) - (l.M : ℂ)⁻¹ • P (U.t i a))
      ((l.M : ℂ)⁻¹ • P (U.t i a))
    rw [sub_add_cancel, k₁] at this
    exact (right_eq_mul.1 this)
  obtain ⟨b, hb⟩ := (U.ex_ker i P hP _).1 k₂
  refine ⟨b, hP.2.1 ?_⟩
  rw [map_add (f := _), map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, ← smul_sub, smul_smul, mul_inv_cancel₀ hM, one_smul]
  abel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalSectionNonzeroAllFibresModuli
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.PushLoc

open LBGerm PushInv ReciprocityTheory.ChartRestriction.G.Out

theorem exists_sec_lpow {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (T : Over S) {V : S.Opens}
    (hV : ∀ y, T.hom y ∈ V) {θ : ∀ i, Γ(A.left, A.hom ⁻¹ᵁ V ⊓ L.U i)} (hθ : θ ∈ secOn L (A.hom ⁻¹ᵁ V))
    (hne : ∀ y ∈ V, ∃ (g : A.left) (i : L.ι), A.hom g = y ∧ g ∈ A.left.basicOpen (θ i)) :
    ∃ s : LB.Sec (LPow A L (1 : ℕ) T), ∀ p : T.left, ∃ (q : (T ⊗ A).left) (i : (LPow A L (1 : ℕ) T).ι),
      (fst T A).left q = p ∧ q ∈ (T ⊗ A).left.basicOpen (s.f i) := by
  have hz : ∀ z, A.hom ((snd T A).left z) ∈ V := fun z => by
    rw [← Scheme.Hom.comp_apply, w_snd, Scheme.Hom.comp_apply]; exact hV _
  have le : ∀ j : Fin 1 → L.ι, (LPow A L (1 : ℕ) T).U j ≤ (snd T A).left ⁻¹ᵁ (A.hom ⁻¹ᵁ V ⊓ L.U (j 0)) :=
    fun j z h => ⟨hz z, (mem_chart A L T _ z j).1 h⟩
  have v : ∀ (j : Fin 1 → L.ι) z, z ∈ (LPow A L (1 : ℕ) T).U j →
      gs (𝟙 _) z _ (((snd T A).left.appLE _ _ (le j)).hom (θ (j 0))) =
        ((snd T A).left.stalkMap z).hom (gs (𝟙 _) _ _ (θ (j 0))) := fun j z h => by
    rw [gs_appLE _ _ _ (le j) (𝟙 _) z h, Category.id_comp]
    exact gs_stalkMap _ z (A.hom ⁻¹ᵁ V ⊓ L.U (j 0)) (le j h) _
  refine ⟨secOfGerm (fun j => ((snd T A).left.appLE _ _ (le j)).hom (θ (j 0)))
    fun z i j hi hj => by
      rw [v i z hi, v j z hj, gm_lpow A L T (𝟙 _) z i j hi hj, Category.id_comp,
        gs_secOn hθ _ (i 0) (j 0) (hz z) (le i hi).2 (le j hj).2, map_mul,
        ← gm_comp _ (𝟙 _) z (L.U (i 0) ⊓ L.U (j 0)) ⟨(le i hi).2, (le j hj).2⟩, Category.comp_id], fun p => ?_⟩
  obtain ⟨g, i, hg, hi⟩ := hne (T.hom p) (hV p)
  obtain ⟨q, h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback T.hom A.hom) p g hg.symm
  obtain rfl : (snd T A).left q = g := h₂
  refine ⟨q, fun _ => i, h₁, ?_⟩
  show q ∈ (T ⊗ A).left.basicOpen (((snd T A).left.appLE _ _ (le fun _ => i)).hom (θ i))
  rw [Scheme.basicOpen_appLE]
  exact ⟨(mem_chart A L T _ q _).2 (A.left.basicOpen_le _ hi).2, hi⟩

theorem exists_secNZ : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (z : Xo.X), ∃ (R : Type) (_ : CommRing R) (_ : IsNoetherianRing R) (j : Sp R ⟶ Xo.X) (θ : LB.Sec (PPx j)), IsOpenImmersion j ∧ z ∈ Set.range j ∧ SecNZ j θ := by
  intro hS E _ _ _ H D l Xo z
  have := Xo.smooth
  have hsm : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  obtain ⟨V, hV, θ, hθ, -, hne⟩ := pushInvertible hS Xo.X (Obj.toPolAV Xo.univ) z
  obtain ⟨B, j, hj, hp, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := Xo.X) (x := z) (U := V) hV
  have hN : IsLocallyNoetherian (Spec B) := isLocallyNoetherian_of_isOpenImmersion j
  obtain ⟨s, hs⟩ := exists_sec_lpow Xo.univ.t.G Xo.univ.t.PP.L (Over.mk j) (V := V) (fun y => hsub ⟨y, rfl⟩) hθ hne
  exact ⟨B, inferInstance, (isLocallyNoetherian_Spec (R := B)).1 hN, j, s, hj, hp, hs⟩

end GlobalTheory.PushLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteDimensionalCuspSectionsVanishingOffDomain
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree

namespace GlobalTheory.CuspSecFinData

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_finite_determining_set_SS
    {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) :
    ∃ N : Set (_root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), N.Finite ∧
      ∀ P ∈ X.SS la, (∀ y ∈ N, P y = 0) → ∀ x ∈ X.dom, P x = 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨X.dom, Set.Subsingleton.finite ?_, fun P _ hP x hx => hP x hx⟩
    intro a _ b _
    funext τ i
    exact i.elim0
  obtain ⟨ε, hε, hla1⟩ := _root_.GlobalTheory.exists_lower_bound_half_max_norm E r X la hr
  obtain ⟨K, hK, hKdom, hKmove⟩ := _root_.GlobalTheory.FlagMahler.mahler_compactness r X ε hε
  obtain ⟨β, hβc, hβ⟩ := _root_.GlobalTheory.GramSchmidtCont.exists_continuous_gramSchmidt r X
  have hcont : ContinuousOn (fun x => _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (β x)) X.dom := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    fun_prop
  set K' := (fun x => _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (β x)) '' K with hK'
  have hK'c : IsCompact K' := hK.image_of_continuousOn (hcont.mono hKdom)
  have hK'dom : K' ⊆ X.dom := by
    rintro _ ⟨x, hx, rfl⟩
    exact _root_.ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X (hKdom hx) (hβ x (hKdom hx)).1
  set δ : ℝ := 1 / (1000 * (r : ℝ) ^ 2 * (1 + ∑ τ, ∑ i, |(la τ i : ℝ)|)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    apply one_div_pos.mpr
    have : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
    have : (0 : ℝ) ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := by positivity
    positivity
  obtain ⟨N, hNK, hNnear⟩ := _root_.GlobalTheory.CuspNet.exists_finset_rmul_near_one X hK'c hK'dom hδpos
  refine ⟨(N : Set (_root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)), N.finite_toSet, ?_⟩
  intro P hP hPN
  have hP' := hP
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.SS at hP'
  obtain ⟨⟨hSec, C, hC⟩, -⟩ := hP'
  have hpz : ∀ x ∈ X.dom, X.pnorm la P x = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨x0, hx0, hx0ne⟩ := hne
    have hx0pos : 0 < X.pnorm la P x0 := lt_of_le_of_ne (_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_nonneg X la P x0) (Ne.symm hx0ne)
    set T : Set ℝ := (fun x => X.pnorm la P x) '' X.dom with hT
    have hTbdd : BddAbove T := ⟨C, by rintro _ ⟨x, hx, rfl⟩; exact hC x hx⟩
    have hTne : T.Nonempty := ⟨_, x0, hx0, rfl⟩
    set S := sSup T with hS
    have hle : ∀ x ∈ X.dom, X.pnorm la P x ≤ S := fun x hx => le_csSup hTbdd ⟨x, hx, rfl⟩
    have hSpos : 0 < S := lt_of_lt_of_le hx0pos (hle x0 hx0)
    obtain ⟨_, ⟨z, hz, rfl⟩, hzS⟩ := exists_lt_of_lt_csSup hTne (half_lt_self hSpos)
    have hzpos : 0 < X.pnorm la P z := lt_trans (half_pos hSpos) hzS
    have hz2 : ∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z := fun x hx => by
      linarith [hle x hx]
    have hεz : ε ≤ X.la1 z := hla1 P hP z hz hz2 hzpos
    obtain ⟨γ, hγ, b, hb, hyK⟩ := hKmove z hz hεz
    set y := _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul z b) with hy
    have hydom : y ∈ X.dom := hKdom hyK
    have hpy : X.pnorm la P y = X.pnorm la P z :=
      _root_.GlobalTheory.NormFactor.pnormInv_holds r X la P hSec γ hγ z hz b hb
    obtain ⟨hβy, hnorm⟩ := hβ y hydom
    set y' := _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul y (β y) with hy'
    have hpy' : X.pnorm la P y' = X.pnorm la P y := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul X la P hSec.2.1 y hydom (β y) hβy
    have hy'K : y' ∈ K' := ⟨y, hyK, rfl⟩
    obtain ⟨A, hA, hAN⟩ := hNnear y' hy'K
    have hnorm' := hnorm
    unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at hnorm'
    have hhalf : S / 2 ≤ X.pnorm la P y' := by rw [hpy', hpy]; exact hzS.le
    obtain ⟨-, hquarter⟩ := _root_.GlobalTheory.pnorm_near_half_max X la P hSec.1 S hle y' hnorm' hhalf A hA
    have hzero : X.pnorm la P (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul y' A) = 0 := by
      rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq, hPN _ (Finset.mem_coe.mpr hAN)]
      simp
    linarith
  intro x hx
  have h := hpz x hx
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq] at h
  have hn := _root_.ReciprocityTheory.ChartRestriction.G.FD.flowTermNormDecay.nfac_pos X la hx
  rcases mul_eq_zero.mp h with h | h
  · exact norm_eq_zero.mp h
  · exact absurd h hn.ne'


open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.CuspSecFinData.finiteDimensional_of_le_holSub : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (r : ℕ) (Comp : Type) [Fintype Comp] (X : Comp → _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (la : ∀ k, _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (W : Submodule ℂ (_root_.Formalism.L2.PjFree.FDSec X)), W ≤ _root_.Formalism.L2.PjFree.holSub X la →
    (∀ P ∈ W, ∀ k, ∀ x ∉ (X k).dom, P k x = 0) → FiniteDimensional ℂ W := by
  intro E _ _ _ r Comp _ X la W hW hoff
  choose N hNfin hN using fun k => exists_finite_determining_set_SS (X k) (la k)
  haveI : ∀ k, Fintype (N k) := fun k => (hNfin k).fintype
  let L : W →ₗ[ℂ] ((k : Comp) → N k → ℂ) :=
    { toFun := fun P k y => P.1 k y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro P hP
    apply Subtype.ext
    funext k x
    show P.1 k x = 0
    have hcusp := _root_.GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub X la (hW P.2) k
    by_cases hx : x ∈ (X k).dom
    · exact hN k _ hcusp (fun y hy => congrFun (congrFun hP k) ⟨y, hy⟩) x hx
    · exact hoff P.1 P.2 k x hx
  exact Module.Finite.of_injective L hinj

end GlobalTheory.CuspSecFinData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
section
noncomputable section

namespace GlobalTheory.TangentLinear

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameTangent

attribute [local instance] Over.cartesianMonoidalCategory

section Comb

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {G : Over X0} [GrpObj G] [IsCommMonObj G]

theorem smT_prod {κ : Type} (s : Finset κ) (a : S) (u : κ → (overAt x0 (DualNumber S) ⟶ G)) :
    smT x0 a (∏ i ∈ s, u i) = ∏ i ∈ s, smT x0 a (u i) := map_prod (smHom x0 a) u s

theorem smT_sum {κ : Type} (s : Finset κ) (c : κ → S) (v : overAt x0 (DualNumber S) ⟶ G) (h0 : smT x0 0 v = 1) :
    smT x0 (∑ i ∈ s, c i) v = ∏ i ∈ s, smT x0 (c i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, smT_add x0 v h0, ih]

theorem combT_combT {m m' : ℕ} (v : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (hv : ∀ j, smT x0 0 (v j) = 1)
    (A : Matrix (Fin m) (Fin m') S) (N : Fin m' → S) :
    combT x0 (fun i => combT x0 v (fun j => A j i)) N = combT x0 v (A.mulVec N) := by
  simp only [combT, smT_prod, smT_smT]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← smT_sum x0 _ _ _ (hv j)]
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => _root_.mul_comm _ _

end Comb

section Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0}

theorem isCombAtG_mulVec {m m' : ℕ} (v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (hv : ∀ j, IsTanAtG t x0 (v j))
    (w : Fin m' → (Sp (DualNumber S) ⟶ t.G.left)) (A : Matrix (Fin m) (Fin m') S) (N : Fin m' → S)
    (w' : Sp (DualNumber S) ⟶ t.G.left) (h1 : ∀ i, IsCombAtG t x0 v (fun j => A j i) (w i))
    (h2 : IsCombAtG t x0 w N w') : IsCombAtG t x0 v (A.mulVec N) w' := by
  have hw : w = fun i => (combT x0 (fun j => ovT (hv j)) (fun j => A j i)).left :=
    funext fun i => ((isCombAtG_iff t x0 (fun j => ovT (hv j)) _ _).1 (h1 i)).symm
  subst hw
  rw [isCombAtG_iff, combT_combT x0 _ (fun j => smT_zero_ovT (hv j))] at h2
  exact (isCombAtG_iff t x0 (fun j => ovT (hv j)) _ _).2 h2

end Group

theorem isCombAt_mulVec (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) {m : ℕ}
    (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hv : ∀ j, IsTanAt x (v j)) {m' : ℕ}
    (w : Fin m' → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (A : Matrix (Fin m) (Fin m') S) (N : Fin m' → S)
    (w' : (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hw : ∀ i, IsCombAt x v (fun j => A j i) (w i))
    (hw' : IsCombAt x w N w') : IsCombAt x v (A.mulVec N) w' :=
  isCombAtG_mulVec (t := Xo.univ.t) (x0 := x) v hv w A N w' hw hw'

end GlobalTheory.TangentLinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianScheme
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem sec_values_complex_fibre : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (y : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx y)), (∀ (a : ℂ) i (pt : Sp ℂ ⟶ Gx y), pt ≫ Formalism.L2.PjFree.gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (scal y a i * s.f i) = a * valAt' pt ((PPx y).U i) (s.f i)) ∧ (SecGen y s ↔ ∃ (i : (PPx y).ι) (pt : Sp ℂ ⟶ Gx y), pt ≫ Formalism.L2.PjFree.gxSnd y = 𝟙 _ ∧ valAt' pt ((PPx y).U i) (s.f i) ≠ 0) ∧ ∀ s' : LB.Sec (PPx y), (∀ i (pt : Sp ℂ ⟶ Gx y), pt ≫ Formalism.L2.PjFree.gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (s'.f i) = valAt' pt ((PPx y).U i) (s.f i)) → ∀ i, s'.f i = s.f i := by
  intro hT E _ _ _ H Dw l Xo y s
  have hsm : Smooth (Formalism.L2.PjFree.gxSnd y) := by
    have := Xo.univ.t.semi.smooth
    exact inferInstanceAs (Smooth (pullback.fst y Xo.univ.t.G.hom))
  have hred : IsReduced (Gx y) :=
    (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ _ (Formalism.L2.PjFree.gxSnd y) hsm).1
  have h1 : ∀ (a : ℂ) i (f : Γ(Gx y, (PPx y).U i)) (pt : Sp ℂ ⟶ Gx y), pt ≫ Formalism.L2.PjFree.gxSnd y = 𝟙 _ →
      valAt' pt ((PPx y).U i) (scal y a i * f) = a * valAt' pt ((PPx y).U i) f := fun a i f pt hp => by
    by_cases h : ⊤ ≤ pt ⁻¹ᵁ (PPx y).U i
    · rw [valAt'_mul]
      exact congrArg (· * _) (valAt'_constFn pt (Formalism.L2.PjFree.gxSnd y) hp _ a h)
    · rw [valAt'_of_not_le pt h, valAt'_of_not_le pt h, mul_zero]
  have h3 : ∀ i (f g : Γ(Gx y, (PPx y).U i)), (∀ pt : Sp ℂ ⟶ Gx y, pt ≫ Formalism.L2.PjFree.gxSnd y = 𝟙 _ →
      valAt' pt ((PPx y).U i) f = valAt' pt ((PPx y).U i) g) → f = g := fun i f g h =>
    ComplexPoints.eq_of_valAt'_eq (Formalism.L2.PjFree.gxSnd y) _ f g fun pt hp _ => h pt hp
  refine ⟨fun a i pt hp => h1 a i _ pt hp, ⟨fun hs => ?_, ?_⟩, fun s' h i => h3 i _ _ (h i)⟩
  · by_contra hne
    have h0 : ∀ i (pt : Sp ℂ ⟶ Gx y), pt ≫ Formalism.L2.PjFree.gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (s.f i) = 0 := fun i pt hp => by
      by_contra h
      exact hne ⟨i, pt, hp, h⟩
    have hall : ∀ (a : ℂ) i, s.f i = scal y a i * s.f i := fun a i => h3 i _ _ fun pt hp => by
      rw [h1 a i _ pt hp, h0 i pt hp, mul_zero]
    exact zero_ne_one ((hs s).unique (hall 0) (hall 1))
  · rintro ⟨j, q, hq, hv⟩ s'
    obtain ⟨s₀, hs₀⟩ := gfp_gen hT y
    obtain ⟨c, hc, -⟩ := hs₀ s
    have hc0 : c ≠ 0 := fun h => hv (by rw [hc j, h1 c j _ q hq, h, zero_mul])
    obtain ⟨b, hb, hu⟩ := hs₀ s'
    refine ⟨b / c, fun i => h3 i _ _ fun pt hp => ?_, fun a ha => ?_⟩
    · rw [h1 _ i _ pt hp, hb i, hc i, h1 _ i _ pt hp, h1 _ i _ pt hp, ← mul_assoc, div_mul_cancel₀ _ hc0]
    · rw [eq_div_iff hc0]
      refine hu _ fun i => h3 i _ _ fun pt hp => ?_
      rw [h1 _ i _ pt hp, ha i, hc i, h1 _ i _ pt hp, h1 _ i _ pt hp, mul_assoc]

end GlobalTheory
end

