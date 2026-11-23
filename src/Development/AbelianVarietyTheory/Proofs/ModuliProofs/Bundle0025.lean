module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTangentLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.LieEtale

theorem existsUnique_dual_lift {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] {k : Type} [Field k]
    (s : Sp (DualNumber k) ⟶ Y) (x₀ : Sp k ⟶ X)
    (h : x₀ ≫ f = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ s) :
    ∃! x : Sp (DualNumber k) ⟶ X,
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x = x₀ ∧ x ≫ f = s := by
  let π : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hsq : ∀ a b : DualNumber k, a.fst = 0 → b.fst = 0 → a * b = 0 := fun a b ha hb => by
    ext <;> simp [ha, hb]
  have hnil : IsNilpotent (RingHom.ker π.hom) :=
    ⟨2, by
      rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
      exact fun a ha b hb => hsq a b ha hb⟩
  have hj : RingHom.ker π.hom ≤ Ideal.jacobson ⊥ := fun a ha =>
    Ideal.mem_sInf.mpr fun {J} hJ => hJ.2.isPrime.mem_of_pow_mem 2 (by
      rw [pow_two, hsq a a ha ha]; exact J.zero_mem)
  refine existsUnique_of_exists_of_unique ?_ fun x₁ x₂ h₁ h₂ =>
    lift_ext_of_unramified f π hπ hj (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
  have : IsLocalHom π.hom := ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    exists_isAffineOpen_pair f (x₀ (IsLocalRing.closedPoint k)) (O := ⊤) trivial
  refine exists_lift_of_smooth_of_isAffineOpen f hU hV hVU π s x₀ h
    (range_subset_opens_of_isLocalRing s ?_) (range_subset_opens_of_isLocalRing x₀ hxV) ?_
  · have e : f (x₀ (IsLocalRing.closedPoint k)) = s (Spec.map π (IsLocalRing.closedPoint k)) :=
      congr($h (IsLocalRing.closedPoint k))
    rw [← Spec_closedPoint (f := π), ← e]
    exact hVU hxV
  · intro R A _ _ _ _ _ _ π' hπ' φ
    have hs : Function.Surjective π' := fun c => (hπ c).imp fun b hb => (hπ' b).trans hb
    have hk : IsNilpotent (RingHom.ker (π' : CommRingCat.of (DualNumber k) →+* CommRingCat.of k)) := by
      convert hnil using 2
      exact RingHom.ext hπ'
    exact ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective φ π' hs hk⟩

section Formal

variable {S : Scheme.{0}} {O k : Type} {P E : Over S}

def Eig {G : Over S} [GrpObj G] (z : P ⟶ E) (sc : k → (E ⟶ E)) (act : O → (G ⟶ G)) (τ : O → k)
    (v : E ⟶ G) : Prop :=
  z ≫ v = 1 ∧ ∀ a, v ≫ act a = sc (τ a) ≫ v

theorem comp_listProd {G : Over S} [GrpObj G] (z : P ⟶ E) (l : List (E ⟶ G))
    (h : ∀ u ∈ l, z ≫ u = 1) : z ≫ l.prod = 1 := by
  induction l with
  | nil => exact MonObj.comp_one z
  | cons u l ih =>
    rw [List.prod_cons, MonObj.comp_mul, h u (by simp), ih fun w hw => h w (by simp [hw]),
      _root_.mul_one]

theorem ofFn_prod_comp {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ] {n : ℕ}
    (u : Fin n → (E ⟶ A)) : (List.ofFn u).prod ≫ ψ = (List.ofFn fun i => u i ≫ ψ).prod :=
  (map_list_prod (IsMonHom.monoidHom ψ E) _).trans (by rw [List.map_ofFn]; rfl)

theorem mult_iff {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ]
    (z : P ⟶ E) (sc : k → (E ⟶ E)) (hz : ∀ c, z ≫ sc c = z)
    (a : O → (A ⟶ A)) (b : O → (B ⟶ B)) (ha : ∀ c, IsMonHom (a c))
    (hab : ∀ c, a c ≫ ψ = ψ ≫ b c) (τ : O → k)
    (H : ∀ w : E ⟶ B, z ≫ w = 1 → ∃! v : E ⟶ A, z ≫ v = 1 ∧ v ≫ ψ = w) (n : ℕ) :
    (∃ v : Fin n → (E ⟶ A), (∀ i, Eig z sc a τ (v i)) ∧ ∀ w, Eig z sc a τ w →
      ∃! c : Fin n → k, w = (List.ofFn fun i => sc (c i) ≫ v i).prod) ↔
    (∃ v : Fin n → (E ⟶ B), (∀ i, Eig z sc b τ (v i)) ∧ ∀ w, Eig z sc b τ w →
      ∃! c : Fin n → k, w = (List.ofFn fun i => sc (c i) ≫ v i).prod) := by
  have htan : ∀ v : E ⟶ A, z ≫ v = 1 → z ≫ v ≫ ψ = 1 := fun v hv => by
    rw [← Category.assoc, hv, MonObj.one_comp]
  have hinj : ∀ v v' : E ⟶ A, z ≫ v = 1 → z ≫ v' = 1 → v ≫ ψ = v' ≫ ψ → v = v' :=
    fun v v' hv hv' e => (H _ (htan v' hv')).unique ⟨hv, e⟩ ⟨hv', rfl⟩
  have hsc : ∀ (c : k) (v : E ⟶ A), z ≫ v = 1 → z ≫ sc c ≫ v = 1 := fun c v hv => by
    rw [← Category.assoc, hz, hv]
  have heig : ∀ v : E ⟶ A, z ≫ v = 1 → (Eig z sc a τ v ↔ Eig z sc b τ (v ≫ ψ)) := fun v hv => by
    refine ⟨fun h => ⟨htan v hv, fun c => ?_⟩, fun h => ⟨hv, fun c => hinj _ _ ?_ (hsc _ _ hv) ?_⟩⟩
    · rw [Category.assoc, ← hab, ← Category.assoc, h.2, Category.assoc]
    · have := ha c
      rw [← Category.assoc, hv, MonObj.one_comp]
    · rw [Category.assoc, hab, ← Category.assoc, h.2, Category.assoc]
  have hcomb : ∀ (v : Fin n → (E ⟶ A)) (w : E ⟶ A), (∀ i, z ≫ v i = 1) → z ≫ w = 1 →
      ∀ c : Fin n → k, (w = (List.ofFn fun i => sc (c i) ≫ v i).prod ↔
        w ≫ ψ = (List.ofFn fun i => sc (c i) ≫ v i ≫ ψ).prod) := fun v w hv hw c => by
    have e : (List.ofFn fun i => sc (c i) ≫ v i).prod ≫ ψ =
        (List.ofFn fun i => sc (c i) ≫ v i ≫ ψ).prod := by
      simp only [ofFn_prod_comp, Category.assoc]
    rw [← e]
    refine ⟨fun h => by rw [← h], hinj _ _ hw (comp_listProd z _ fun u hu => ?_)⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    exact hsc _ _ (hv i)
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨fun i => v i ≫ ψ, fun i => (heig _ (hv i).1).mp (hv i), fun w hw => ?_⟩
    obtain ⟨w', ⟨hw', rfl⟩, -⟩ := H w hw.1
    exact (existsUnique_congr (hcomb v w' (fun i => (hv i).1) hw')).mp (h w' ((heig _ hw').mpr hw))
  · rintro ⟨v, hv, h⟩
    choose v' hv' using fun i => (H (v i) (hv i).1).exists
    obtain rfl : v = fun i => v' i ≫ ψ := funext fun i => (hv' i).2.symm
    refine ⟨v', fun i => (heig _ (hv' i).1).mpr (hv i), fun w hw => ?_⟩
    exact (existsUnique_congr (hcomb v' w (fun i => (hv' i).1) hw.1)).mpr
      (h _ ((heig _ hw.1).mp hw))

end Formal

section Dual

variable {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S)

def epsPtZero : Over.mk x ⟶ epsPt x :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (by
    change _ ≫ _ ≫ x = x
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) =
      RingHom.id k := RingHom.ext fun _ => rfl
    rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp])

def epsPtScale (c : k) : epsPt x ⟶ epsPt x :=
  Over.homMk (spMap (epsScale c)) (by
    change _ ≫ _ ≫ x = _ ≫ x
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).commutes r)

theorem epsPtZero_epsPtScale (c : k) : epsPtZero x ≫ epsPtScale x c = epsPtZero x := by
  refine Over.OverMorphism.ext ?_
  change spMap _ ≫ spMap _ = spMap _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun r => TrivSqZeroExt.fst_map _ r

variable {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (τ : O →+* k)

theorem isLieEigen_iff (v : epsPt x ⟶ G) :
    IsLieEigen act x τ v ↔ Eig (epsPtZero x) (epsPtScale x) act.act τ v :=
  ⟨fun h => ⟨Over.OverMorphism.ext h.1, fun a => Over.OverMorphism.ext (h.2 a)⟩,
    fun h => ⟨congrArg (·.left) h.1, fun a => congrArg (·.left) (h.2 a)⟩⟩

theorem lieMult_iff (n : ℕ) : LieMult act x τ n ↔
    ∃ v : Fin n → (epsPt x ⟶ G), (∀ i, Eig (epsPtZero x) (epsPtScale x) act.act τ (v i)) ∧
      ∀ w, Eig (epsPtZero x) (epsPtScale x) act.act τ w →
        ∃! c : Fin n → k, w = (List.ofFn fun i => epsPtScale x (c i) ≫ v i).prod := by
  simp only [LieMult, isLieEigen_iff]
  refine exists_congr fun v => and_congr_right fun _ => forall_congr' fun w =>
    imp_congr_right fun _ => existsUnique_congr fun c => ⟨?_, fun h => ⟨_, fun _ => rfl, h⟩⟩
  rintro ⟨u, hu, rfl⟩
  obtain rfl : u = fun i => epsPtScale x (c i) ≫ v i :=
    funext fun i => Over.OverMorphism.ext (hu i)
  rfl

theorem existsUnique_tangent_lift {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ]
    [Etale ψ.left] (w : epsPt x ⟶ B) (hw : epsPtZero x ≫ w = 1) :
    ∃! v : epsPt x ⟶ A, epsPtZero x ≫ v = 1 ∧ v ≫ ψ = w := by
  obtain ⟨v, ⟨h₁, h₂⟩, hu⟩ := existsUnique_dual_lift ψ.left w.left (1 : Over.mk x ⟶ A).left
    (congrArg (·.left) ((MonObj.one_comp ψ).trans hw.symm))
  refine ⟨Over.homMk v ?_, ⟨Over.OverMorphism.ext h₁, Over.OverMorphism.ext h₂⟩,
    fun v' hv' => Over.OverMorphism.ext
      (hu _ ⟨congrArg (·.left) hv'.1, congrArg (·.left) hv'.2⟩)⟩
  rw [← Over.w ψ, ← Category.assoc]
  exact (congrArg (· ≫ B.hom) h₂).trans (Over.w w)

end Dual

theorem lieMult_iff_of_etale :
    ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (a : OAct O A) (b : OAct O B), IsMonHom ψ → Etale ψ.left → (∀ c, a.act c ≫ ψ = ψ ≫ b.act c) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (τ : O →+* k) (n : ℕ), LieMult a x τ n ↔ LieMult b x τ n := by
  intro O _ S A B _ _ ψ a b _ _ hab k _ x τ n
  rw [lieMult_iff, lieMult_iff]
  exact mult_iff ψ _ _ (epsPtZero_epsPtScale x) a.act b.act a.hom hab τ
    (existsUnique_tangent_lift x ψ) n

end GlobalTheory.LieEtale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsVeryGeneralPointOfHolomorphicFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_veryGeneral_point_of_holomorphic_family :
    ∀ (o : Type) [CommRing o] [Countable o] (em : o →+* ℂ) (I : Type) [Countable I] (m : ℕ) (B : Set (Fin m → ℂ)) (θ : (Fin m → ℂ) → I → ℂ), IsOpen B → IsPreconnected B → B.Nonempty → (∀ a, DifferentiableOn ℂ (fun z => θ z a) B) → ∃ z ∈ B, ∃ c : ℂ, c ≠ 0 ∧ ∀ F : MvPolynomial I o, MvPolynomial.eval₂ em (c • θ z) F = 0 → ∀ z' ∈ B, ∀ c' : ℂ, c' ≠ 0 → MvPolynomial.eval₂ em (c' • θ z') F = 0 := by
  intro o _ _ em I _ m B θ hB hBc hBne hθ
  classical
  have : Countable (MvPolynomial I o) :=
    Function.Surjective.countable
      (f := (AddMonoidAlgebra.ofCoeff : ((I →₀ ℕ) →₀ o) → MvPolynomial I o))
      fun F => ⟨AddMonoidAlgebra.coeff F, rfl⟩

  set Ω : Set (Fin (m + 1) → ℂ) := {p | Fin.tail p ∈ B ∧ p 0 ∈ ({0}ᶜ : Set ℂ)} with hΩ
  have htail : Differentiable ℂ (fun p : Fin (m + 1) → ℂ => Fin.tail p) :=
    differentiable_pi.2 fun i => differentiable_apply _
  have hhead : Differentiable ℂ (fun p : Fin (m + 1) → ℂ => p 0) := differentiable_apply _
  have hΩo : IsOpen Ω :=
    (hB.preimage htail.continuous).inter (isOpen_compl_singleton.preimage hhead.continuous)
  have hΩimg : Ω = (fun q : (Fin m → ℂ) × ℂ => (Fin.cons q.2 q.1 : Fin (m + 1) → ℂ)) ''
      (B ×ˢ ({0}ᶜ : Set ℂ)) := by
    ext p
    constructor
    · intro hp
      exact ⟨(Fin.tail p, p 0), ⟨hp.1, hp.2⟩, Fin.cons_self_tail p⟩
    · rintro ⟨⟨z, c⟩, ⟨hz, hc⟩, rfl⟩
      exact ⟨by simpa using hz, by simpa using hc⟩
  have hΩc : IsPreconnected Ω := by
    rw [hΩimg]
    refine (hBc.prod (isConnected_compl_singleton_of_one_lt_rank ?_ 0).isPreconnected).image _ ?_
    · rw [Complex.rank_real_complex]; norm_num
    · exact (Continuous.finCons (A := fun _ => ℂ) continuous_snd continuous_fst).continuousOn
  have hΩne : Ω.Nonempty := by
    obtain ⟨z₀, hz₀⟩ := hBne
    exact ⟨Fin.cons 1 z₀, by simpa using hz₀, by simp⟩

  let f : MvPolynomial I o → (Fin (m + 1) → ℂ) → ℂ :=
    fun F p => MvPolynomial.eval₂ em (p 0 • θ (Fin.tail p)) F
  have hfd : ∀ F, DifferentiableOn ℂ (f F) Ω := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a =>
      simp only [f, MvPolynomial.eval₂_C]
      exact differentiableOn_const _
    | add F G hF hG =>
      simp only [f, MvPolynomial.eval₂_add]
      exact hF.add hG
    | mul_X F a hF =>
      have ha : DifferentiableOn ℂ (fun p : Fin (m + 1) → ℂ => θ (Fin.tail p) a) Ω :=
        (hθ a).comp htail.differentiableOn fun p hp => hp.1
      simp only [f, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Pi.smul_apply, smul_eq_mul]
      exact hF.mul (hhead.differentiableOn.mul ha)
  have hfa : ∀ F, AnalyticOnNhd ℂ (f F) Ω := fun F =>
    ReciprocityTheory.AnForm.Osgood.osgood (m + 1) Ω (f F) hΩo (hfd F)

  let W : MvPolynomial I o → Set (Fin (m + 1) → ℂ) := fun F =>
    if Set.EqOn (f F) 0 Ω then Set.univ else (Ω ∩ f F ⁻¹' {0}ᶜ) ∪ (closure Ω)ᶜ
  have hWo : ∀ F, IsOpen (W F) := by
    intro F
    by_cases h : Set.EqOn (f F) 0 Ω
    · simp only [W, if_pos h]
      exact isOpen_univ
    · simp only [W, if_neg h]
      exact ((hfd F).continuousOn.isOpen_inter_preimage hΩo isOpen_compl_singleton).union
        isClosed_closure.isOpen_compl
  have hWd : ∀ F, Dense (W F) := by
    intro F
    by_cases h : Set.EqOn (f F) 0 Ω
    · simp only [W, if_pos h]
      exact dense_univ
    · simp only [W, if_neg h]
      have hsub : Ω ⊆ closure (Ω ∩ f F ⁻¹' {0}ᶜ) := by
        intro q hq
        by_contra hq'
        apply h
        refine (hfa F).eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩc hq ?_
        have hn : (closure (Ω ∩ f F ⁻¹' {0}ᶜ))ᶜ ∩ Ω ∈ nhds q :=
          Filter.inter_mem (isClosed_closure.isOpen_compl.mem_nhds hq') (hΩo.mem_nhds hq)
        filter_upwards [hn] with p hp
        by_contra hne
        exact hp.1 (subset_closure ⟨hp.2, hne⟩)
      intro x
      by_cases hx : x ∈ closure Ω
      · exact closure_mono Set.subset_union_left (closure_minimal hsub isClosed_closure hx)
      · exact subset_closure (Or.inr hx)

  obtain ⟨p, hpΩ, hpW⟩ := (dense_iInter_of_isOpen hWo hWd).inter_open_nonempty Ω hΩo hΩne
  refine ⟨Fin.tail p, hpΩ.1, p 0, hpΩ.2, fun F hF z' hz' c' hc' => ?_⟩
  by_cases h : Set.EqOn (f F) 0 Ω
  · have hmem : (Fin.cons c' z' : Fin (m + 1) → ℂ) ∈ Ω := ⟨by simpa using hz', by simpa using hc'⟩
    simpa [f] using h hmem
  · have hpW' := Set.mem_iInter.1 hpW F
    simp only [W, if_neg h] at hpW'
    rcases hpW' with hp' | hp'
    · exact absurd hF hp'.2
    · exact absurd (subset_closure hpΩ) hp'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankMapAddFinrankInfKerOfFinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open MvPolynomial

theorem finrank_map_add_finrank_inf_ker_of_finite {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (P : Submodule K M) [Module.Finite K P] :
    Module.finrank K ↥(P.map f) + Module.finrank K ↥(P ⊓ LinearMap.ker f) = Module.finrank K P := by
  have h := (f.domRestrict P).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq P, Submodule.map_comap_subtype] at h
  exact h

theorem mem_homogeneousSubmodule_mul_of_add {K σ : Type*} [Field K] {m n : ℕ}
    {F : MvPolynomial σ K} (hF : F.IsHomogeneous (m + n)) :
    F ∈ homogeneousSubmodule σ K m * homogeneousSubmodule σ K n := by
  rw [← homogeneousSubmodule_one_pow K m, ← homogeneousSubmodule_one_pow K n, ← pow_add,
    homogeneousSubmodule_one_pow]
  exact hF

theorem sub_rename_mem_span_degree {K σ : Type*} [Field K] (t : σ → σ)
    (I : Ideal (MvPolynomial σ K)) (hI : ∀ F, F - rename t F ∈ I) {d : ℕ} (hd : 1 ≤ d)
    {e : ℕ} (he : d ≤ e) : ∀ F : MvPolynomial σ K, F.IsHomogeneous e →
      F - rename t F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by
  have hk : ∀ (l : MvPolynomial σ K), l.IsHomogeneous 1 → l ∈ I → ∀ n, d ≤ n →
      ∀ H : MvPolynomial σ K, H.IsHomogeneous n →
      l * H ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by
    intro l hl hlI n hn H hH
    have hn' : n = (d - 1) + (n - (d - 1)) := by omega
    rw [hn'] at hH
    refine Submodule.mul_induction_on (mem_homogeneousSubmodule_mul_of_add hH) ?_ ?_
    · intro A hA B _
      rw [← _root_.mul_assoc]
      refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨Ideal.mul_mem_right _ _ hlI, ?_⟩)
      have h := hl.mul hA
      rwa [show 1 + (d - 1) = d by omega] at h
    · intro x y hx hy
      rw [mul_add]
      exact add_mem hx hy
  induction e, he using Nat.le_induction with
  | base =>
    intro F hF
    exact Ideal.subset_span ⟨hI F, hF.sub hF.rename_isHomogeneous⟩
  | succ n hn ih =>
    intro F hF
    rw [add_comm] at hF
    refine Submodule.mul_induction_on (mem_homogeneousSubmodule_mul_of_add hF) ?_ ?_
    · intro l hl G hG
      have hl' : l.IsHomogeneous 1 := hl
      have hG' : G.IsHomogeneous n := hG
      have : l * G - rename t (l * G) =
          l * (G - rename t G) + (l - rename t l) * rename t G := by
        rw [map_mul]; ring
      rw [this]
      exact add_mem (Ideal.mul_mem_left _ _ (ih G hG'))
        (hk _ (hl'.sub hl'.rename_isHomogeneous) (hI l) n hn _ hG'.rename_isHomogeneous)
    · intro x y hx hy
      have : x + y - rename t (x + y) = (x - rename t x) + (y - rename t y) := by
        rw [map_add (f := _)]; ring
      rw [this]
      exact add_mem hx hy

theorem regularity_comap_rename_of_surjective :
    ∀ (σ σ₀ : Type) [Finite σ] [Finite σ₀] [Nonempty σ₀] (r : σ → σ₀) (Q₀ : Polynomial ℚ), Function.Surjective r → ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] (I₀ : Ideal (MvPolynomial σ₀ K)) (I : Ideal (MvPolynomial σ K)) (d : ℕ), I = I₀.comap (MvPolynomial.rename r) → 1 ≤ d → ∀ e ≥ d, (((Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ₀ K e ⊓ (I₀).restrictScalars K) : ℕ) : ℚ) = Q₀.eval (e : ℚ) → ((Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e ⊓ (I).restrictScalars K) : ℕ) : ℚ) = Q.eval (e : ℚ)) ∧ ((∀ F ∈ I₀, F.IsHomogeneous e → F ∈ Ideal.span {G | G ∈ I₀ ∧ G.IsHomogeneous d}) → ∀ F ∈ I, F.IsHomogeneous e → F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d}) := by
  intro σ σ₀ _ _ _ r Q₀ hr
  obtain ⟨s, hs⟩ := hr.hasRightInverse
  haveI : Nonempty σ := ⟨s (Classical.arbitrary _)⟩
  obtain ⟨P, hP⟩ := _root_.GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule σ
  obtain ⟨P₀, hP₀⟩ := _root_.GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule σ₀
  refine ⟨Q₀ + P - P₀, ?_⟩
  intro K _ I₀ I d hI hd e he
  have hrs : ∀ G : MvPolynomial σ₀ K, rename r (rename s G) = G := by
    intro G
    rw [rename_rename, hs.comp_eq_id, rename_id_apply]
  have hmem : ∀ F, F ∈ I ↔ rename r F ∈ I₀ := by
    intro F
    rw [hI]; exact Ideal.mem_comap
  constructor
  · intro h
    haveI : Module.Finite K (homogeneousSubmodule σ K e) :=
      Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
    haveI : Module.Finite K ↥(homogeneousSubmodule σ K e ⊓ I.restrictScalars K) :=
      Submodule.finiteDimensional_of_le inf_le_left
    have h1 := finrank_map_add_finrank_inf_ker_of_finite
      (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap (homogeneousSubmodule σ K e)
    have h2 := finrank_map_add_finrank_inf_ker_of_finite
      (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap
      (homogeneousSubmodule σ K e ⊓ I.restrictScalars K)
    have e1 : (homogeneousSubmodule σ K e).map
        (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap =
        homogeneousSubmodule σ₀ K e := by
      apply le_antisymm
      · rintro _ ⟨F, hF, rfl⟩
        exact IsHomogeneous.rename_isHomogeneous hF
      · intro G hG
        exact ⟨rename s G, IsHomogeneous.rename_isHomogeneous hG, hrs G⟩
    have e2 : (homogeneousSubmodule σ K e ⊓ I.restrictScalars K).map
        (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap =
        homogeneousSubmodule σ₀ K e ⊓ I₀.restrictScalars K := by
      apply le_antisymm
      · rintro _ ⟨F, hF, rfl⟩
        exact ⟨IsHomogeneous.rename_isHomogeneous hF.1, (hmem F).1 hF.2⟩
      · intro G hG
        refine ⟨rename s G, ⟨IsHomogeneous.rename_isHomogeneous hG.1, (hmem _).2 ?_⟩, hrs G⟩
        rw [hrs]; exact hG.2
    have e3 : homogeneousSubmodule σ K e ⊓ I.restrictScalars K ⊓ LinearMap.ker
        (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap =
        homogeneousSubmodule σ K e ⊓ LinearMap.ker
        (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap := by
      apply le_antisymm
      · exact inf_le_inf_right _ inf_le_left
      · intro F hF
        refine ⟨⟨hF.1, (hmem F).2 ?_⟩, hF.2⟩
        have : rename r F = 0 := hF.2
        rw [this]; exact zero_mem _
    rw [e1] at h1
    rw [e2, e3] at h2
    rw [Polynomial.eval_sub, Polynomial.eval_add, ← h, ← hP K e, ← hP₀ K e, ← h1, ← h2]
    push_cast
    ring
  · intro h F hF hFe
    have hA := sub_rename_mem_span_degree (s ∘ r) I (fun G => by
      rw [hmem, map_sub, ← rename_rename, hrs, sub_self]; exact zero_mem _) hd he F hFe
    have hB : Ideal.span {G | G ∈ I₀ ∧ G.IsHomogeneous d} ≤
        (Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d}).comap (rename s) := by
      rw [Ideal.span_le]
      intro G hG
      refine Ideal.mem_comap.mpr (Ideal.subset_span ⟨(hmem _).2 ?_, hG.2.rename_isHomogeneous⟩)
      rw [hrs]; exact hG.1
    have hC := Ideal.mem_comap.mp (hB (h _ ((hmem F).1 hF) hFe.rename_isHomogeneous))
    rw [rename_rename] at hC
    simpa using add_mem hA hC

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapsOfParts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem levelMaps_of_parts : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∃ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F) (rF : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom → IsFinite rF ∧ Etale rF ∧ Surjective rF) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F) (rF : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom → ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Xo₂.XF c₂), y ≫ rF = y' ≫ rF → (∃ (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ ∧ Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r ∧ y' ≫ pullback.fst _ _ = y ≫ pullback.fst _ _ ≫ ρ.hom) ∧ ∀ (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ → Xo₂.LevAut g ρ → y ≫ pullback.fst _ _ ≫ ρ.hom = y ≫ pullback.fst _ _ → g.TrivAt l₂) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) := by
  intro h₁ h₂ h₃ h₄ E _ _ _ H D hpq l l₂ Xo Xo₂ hd
  obtain ⟨r, jK, m, hh⟩ := h₁ E H D l l₂ Xo Xo₂ hpq hd
  refine ⟨r, jK, m, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2, h₂ E H D l l₂ Xo Xo₂ hpq hd r jK m hh, ?_⟩
  intro c c₂ hc
  have hring : (IntermediateField.inclusion c₂.le).toRingHom.comp jK =
      (IntermediateField.inclusion hc.le).toRingHom.comp (IntermediateField.inclusion c.le).toRingHom := by
    ext x
    exact hh.1 x
  have w : (pullback.fst Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫ r) ≫ Xo.s =
      (pullback.snd Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫
        spMap (IntermediateField.inclusion hc.le).toRingHom) ≫
        spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [Category.assoc, hh.2.1, pullback.condition_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hring]
  have e₁ := pullback.lift_fst _ _ w
  have e₂ := pullback.lift_snd _ _ w
  have k₃ := h₃ E H D l l₂ Xo Xo₂ hpq hd r jK m hh c c₂ hc _ e₁ e₂
  exact ⟨pullback.lift _ _ w, e₁, e₂, k₃.1, k₃.2.1, k₃.2.2,
    h₄ E H D l l₂ Xo Xo₂ hpq hd r jK m hh c c₂ hc _ e₁ e₂⟩

end GlobalTheory
end

