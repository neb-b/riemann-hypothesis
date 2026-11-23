module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.WtMatFix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RestrictAutomorphism
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0030
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AinfActionTiltFixedOfFrobeniusRelation
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

namespace UpperTheory.V.Loc

variable {l : ℕ} [hl : Fact l.Prime]

open Polynomial in
open scoped Formalism.Per in
private theorem tfab_lift (y : OCb l) {m : ℕ} (hm : 0 < m) (hy : y ^ l ^ m = y) :
    ∃ (z : OC l) (x : Om l), (z : ℂ_[l]) = (x : ℂ_[l]) ∧ x ^ l ^ m = x ∧
      PreTilt.coeff 0 y = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) z := by
  have h1 : 1 < l ^ m := Nat.one_lt_pow hm.ne' hl.out.one_lt
  have hz : y.untilt ^ l ^ m = y.untilt := by rw [← map_pow, hy]
  have hz' : ((y.untilt : OC l) : ℂ_[l]) ^ l ^ m = (y.untilt : OC l) := by
    have := congrArg (fun t : OC l => (t : ℂ_[l])) hz
    simpa using this
  have hint : IsIntegral (Om l) ((y.untilt : OC l) : ℂ_[l]) := by
    refine ⟨X ^ l ^ m - X, monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1), ?_⟩
    simp [hz']
  obtain ⟨x, hx⟩ := minpoly.mem_range_of_degree_eq_one (Om l) _
    (IsAlgClosed.degree_eq_one_of_irreducible (Om l) (minpoly.irreducible hint))
  refine ⟨y.untilt, x, hx.symm, ?_, (PreTilt.mk_untilt_eq_coeff_zero y).symm⟩
  apply (algebraMap (Om l) ℂ_[l]).injective
  have hx' : algebraMap (Om l) ℂ_[l] x = (y.untilt : OC l) := hx
  rw [map_pow, hx', hz']

private theorem tfab_root {x : Om l} {m : ℕ} (hm : 0 < m) (hx : x ^ l ^ m = x) (h0 : x ≠ 0) :
    ∃ n, 0 < n ∧ ¬ l ∣ n ∧ x ^ n = 1 := by
  have h1 : 1 < l ^ m := Nat.one_lt_pow hm.ne' hl.out.one_lt
  refine ⟨l ^ m - 1, by omega, fun h => ?_, ?_⟩
  · have h2 := (Nat.dvd_sub_iff_right h1.le (dvd_pow_self l hm.ne')).mp h
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h2)
  · apply mul_right_cancel₀ h0
    rw [← pow_succ, one_mul, Nat.sub_add_cancel h1.le, hx]

end UpperTheory.V.Loc

theorem UpperTheory.Ainf_action_tilt_fixed_of_frobenius_relation :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l) (a b : ℕ), (∀ c : ↥(MaximalUnramifiedExtension l), g (((GlobalTheory.Pst.frobUr l ^ b) c : ↥(MaximalUnramifiedExtension l)) : Om l) = (((GlobalTheory.Pst.frobUr l ^ a) c : ↥(MaximalUnramifiedExtension l)) : Om l)) → ∀ (y : OCb l) (m : ℕ), 0 < m → y ^ l ^ m = y → AI.actT g (y ^ l ^ b) = y ^ l ^ a := by
  intro l hl P AI g a b hg y m hm hy
  obtain ⟨z, x, hzx, hx, h0⟩ := UpperTheory.V.Loc.tfab_lift y hm hy
  have hgx : g (x ^ l ^ b) = x ^ l ^ a := by
    by_cases hx0 : x = 0
    · rw [hx0, zero_pow (pow_ne_zero _ hl.out.ne_zero), zero_pow (pow_ne_zero _ hl.out.ne_zero), map_zero]
    obtain ⟨n, hn0, hn, hxn⟩ := UpperTheory.V.Loc.tfab_root hm hx hx0
    have hmem : x ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨n, hn0, hn, hxn⟩
    have h1 := hg ⟨x, hmem⟩
    rw [GlobalTheory.Pst.frobUr_pow_root b ⟨x, hmem⟩ n hn0 hn (Subtype.ext hxn),
      GlobalTheory.Pst.frobUr_pow_root a ⟨x, hmem⟩ n hn0 hn (Subtype.ext hxn)] at h1
    exact h1
  have hc : ∀ k : ℕ, PreTilt.coeff 0 (y ^ k) = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (z ^ k) := fun k => by
    rw [map_pow, h0]
    exact (map_pow _ _ _).symm
  have hz : ∀ k : ℕ, ((z ^ k : OC l) : ℂ_[l]) = ((x ^ k : Om l) : ℂ_[l]) := fun k => by
    rw [PadicComplex.coe_eq, map_pow, ← PadicComplex.coe_eq, ← hzx]
    simp
  have hp : ∀ k : ℕ, (y ^ k) ^ l ^ m = y ^ k := fun k => by rw [← pow_mul, mul_comm, pow_mul, hy]
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g (y ^ l ^ b) 0 _ (hc _)
  rw [hz, AI.actC_ext, hgx, ← hz] at h1
  refine GlobalTheory.UnramifiedCrys.eq_of_coeff_zero hm (by rw [← map_pow, hp]) (hp _) ?_
  rw [h2, hc, Subtype.ext h1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CrUnipChar
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

noncomputable section

namespace UpperTheory.V.Loc.CrUnipChar

variable {Q A B : Type} [Field Q] [CommRing A] [Algebra Q A] [AddCommGroup B] [Module Q B]

private def ctr (lam : A →ₗ[Q] Q) : A ⊗[Q] B →ₗ[Q] B :=
  (TensorProduct.lid Q B).toLinearMap ∘ₗ lam.rTensor B

private theorem ctr_tmul (lam : A →ₗ[Q] Q) (a : A) (b : B) : ctr lam (a ⊗ₜ[Q] b) = lam a • b := by
  simp [ctr]

private theorem eq_sum [Module.Finite Q A] (x : A ⊗[Q] B) :
    x = ∑ i, Module.finBasis Q A i ⊗ₜ[Q] ctr ((Module.finBasis Q A).coord i) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [ctr_tmul, ← smul_tmul, ← sum_tmul, Basis.coord_apply, Basis.sum_repr]
  | add y z hy hz =>
    simp only [map_add (f := _), tmul_add, Finset.sum_add_distrib]
    rw [← hy, ← hz]

private theorem mem_iff [Module.Finite Q A] (F : Submodule Q B) (x : A ⊗[Q] B) :
    x ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) F.subtype) ↔
      ∀ lam : A →ₗ[Q] Q, ctr lam x ∈ F := by
  constructor
  · rintro ⟨y, rfl⟩ lam
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simpa [ctr_tmul] using F.smul_mem _ b.2
    | add y z hy hz => simpa only [map_add (f := _)] using F.add_mem hy hz
  · intro h
    rw [eq_sum x]
    exact Submodule.sum_mem _ fun i _ => ⟨Module.finBasis Q A i ⊗ₜ ⟨_, h ((Module.finBasis Q A).coord i)⟩, by simp⟩

private theorem ctr_map (lam : A →ₗ[Q] Q) (u : A) (s : B →ₗ[Q] B) (x : A ⊗[Q] B) :
    ctr lam (AlgebraTensorModule.map (u • (LinearMap.id : A →ₗ[A] A)) s x) =
      s (ctr lam x) + s (ctr (lam ∘ₗ LinearMap.mulLeft Q (u - 1)) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [ctr_tmul, sub_mul, sub_smul]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]; abel

private theorem step [Module.Finite Q A] {G : Type} (u : G → A) (hu : ∀ g, IsNilpotent (u g - 1))
    (s : G → B →ₗ[Q] B) (F F' : Submodule Q B) (hs : ∀ g, ∀ b ∈ F', s g b ∈ F')
    (hT : ∀ b ∈ F, (∀ g, s g b - b ∈ F') → b ∈ F') (x : A ⊗[Q] B)
    (hx : ∀ g, AlgebraTensorModule.map (u g • (LinearMap.id : A →ₗ[A] A)) (s g) x = x)
    (hF : ∀ lam : A →ₗ[Q] Q, ctr lam x ∈ F) (lam : A →ₗ[Q] Q) : ctr lam x ∈ F' := by
  haveI : IsNoetherianRing A := isNoetherian_of_tower Q inferInstance
  obtain ⟨k, hk⟩ := IsNoetherianRing.isNilpotent_nilradical A
  have key : ∀ (j : ℕ) (lam : A →ₗ[Q] Q), (∀ a ∈ nilradical A ^ j, lam a = 0) → ctr lam x ∈ F' := by
    intro j
    induction j with
    | zero =>
      intro lam h
      have : lam = 0 := LinearMap.ext fun a => h a (by simp)
      simp [this, ctr]
    | succ j ih =>
      intro lam h
      refine hT _ (hF lam) fun g => ?_
      have e := ctr_map lam (u g) (s g) x
      rw [hx g] at e
      have h2 := hs g _ (ih (lam ∘ₗ LinearMap.mulLeft Q (u g - 1)) fun a ha => h _ (by
        rw [pow_succ']
        exact Ideal.mul_mem_mul (mem_nilradical.2 (hu g)) ha))
      have e2 : s g (ctr lam x) - ctr lam x = -s g (ctr (lam ∘ₗ LinearMap.mulLeft Q (u g - 1)) x) := by
        rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, ← e, sub_self]
      rw [e2]
      exact F'.neg_mem h2
  refine key k lam fun a ha => ?_
  rw [hk] at ha
  rw [(Submodule.mem_bot _).1 ha, map_zero]

private theorem eq_one_of_pow [CharZero Q] {u : A} (hu : IsNilpotent (u - 1)) {n : ℕ} (hn : n ≠ 0)
    (h : u ^ n = 1) : u = 1 := by
  have h1 : IsNilpotent (∑ i ∈ Finset.range n, (u ^ i - 1)) := by
    refine isNilpotent_sum fun i _ => ?_
    obtain ⟨c, hc⟩ := sub_one_dvd_pow_sub_one u i
    rw [hc]
    exact (Commute.all _ _).isNilpotent_mul_right hu
  have h2 : IsUnit ((n : ℕ) : A) := by
    rw [← map_natCast (algebraMap Q A)]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn)).map _
  have h3 : IsUnit (∑ i ∈ Finset.range n, u ^ i) := by
    have := h1.isUnit_add_left_of_commute h2 (Commute.all _ _)
    simpa [Finset.sum_sub_distrib] using this
  have h4 := geom_sum_mul u n
  rw [h, sub_self] at h4
  exact sub_eq_zero.1 (h3.mul_right_eq_zero.1 h4)

private theorem fil {l : ℕ} [Fact l.Prime] {G : Type} [Group G] (φ : G →* GQ l) (K : FinExt l)
    (hK : φ.range = GK K) {A : Type} [CommRing A] [Algebra ℚ_[l] A] [Module.Finite ℚ_[l] A] (κ : G →* Aˣ)
    (hκ : ∀ g, IsNilpotent ((κ g : A) - 1)) :
    FilD φ (chRep κ) 0 = Ddr φ (chRep κ) ∧ FilD φ (chRep κ) 1 = ⊥ := by
  obtain ⟨T⟩ := tiedP l
  let F : ℤ → Submodule ℚ_[l] (Bdr l) := fun a => (((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l]
  have hF : ∀ a b, b ∈ F a ↔ b ∈ ((PP l).PD K).Fil a := fun a b => by
    have := (PP l).PD_Fil (botExt l) K a
    exact Set.ext_iff.1 this b
  have hanti : Antitone F := antitone_int_of_succ_le fun a b hb =>
    (hF _ _).2 (((PP l).PD K).Fil_anti a ((hF _ _).1 hb))
  have up : ∀ x ∈ Ddr φ (chRep κ), ∀ n : ℤ, n ≠ 0 → (∀ lam, ctr lam x ∈ F n) →
      ∀ lam, ctr lam x ∈ F (n + 1) := by
    intro x hx n hn h
    refine step (fun g => (κ g : A)) hκ (fun g => ((PP l).actQdR (φ g)).toLinearMap) (F n) (F (n + 1))
      (fun g b hb => ?_) (fun b hb hg => ?_) x (fun g => ?_) h
    · have := ((PP l).PD K).Fil_G ⟨φ g, by rw [← hK]; exact ⟨g, rfl⟩⟩ _ _ ((hF _ _).1 hb)
      rw [(PP l).PD_actdR] at this
      exact (hF _ _).2 this
    · obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l _ _ T
      obtain ⟨c, -, -, h0, h1⟩ := GlobalTheory.DRFil.graded_invariants T Θ K n b ((hF _ _).1 hb) fun g => by
        obtain ⟨g', hg'⟩ : (g : GQ l) ∈ φ.range := by rw [hK]; exact g.2
        rw [(PP l).PD_actdR, ← hg']
        exact (hF _ _).1 (hg g')
      rw [h0 hn, sub_zero] at h1
      exact (hF _ _).2 h1
    · have := (Submodule.mem_iInf _).1 hx g
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
      exact this
  constructor
  · refine inf_eq_left.2 fun x hx => (mem_iff (F 0) x).2 ?_
    have ex : ∃ a : ℤ, ∀ lam, ctr lam x ∈ F a := by
      clear hx
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨0, fun lam => by simp⟩
      | tmul a b =>
        obtain ⟨n, hn⟩ := ((PP l).PD K).Fil_exh b
        exact ⟨n, fun lam => by rw [ctr_tmul]; exact (F n).smul_mem _ ((hF _ _).2 hn)⟩
      | add y z hy hz =>
        obtain ⟨a, ha⟩ := hy
        obtain ⟨b, hb⟩ := hz
        exact ⟨min a b, fun lam => by
          rw [map_add (f := _)]
          exact (F _).add_mem (hanti (min_le_left _ _) (ha lam)) (hanti (min_le_right _ _) (hb lam))⟩
    obtain ⟨a, ha⟩ := ex
    rcases le_total 0 a with h | h
    · exact fun lam => hanti h (ha lam)
    have key : ∀ m, a ≤ m → m ≤ 0 → ∀ lam, ctr lam x ∈ F m := by
      intro m hm
      induction m, hm using Int.leInduction with
      | base => exact fun _ => ha
      | succ m hm ih => exact fun h => up x hx m (by omega) (ih (by omega))
    exact key 0 h le_rfl
  · refine eq_bot_iff.2 fun x hx => ?_
    have h1 := (mem_iff (F 1) x).1 hx.2
    have key : ∀ m : ℤ, 1 ≤ m → ∀ lam, ctr lam x ∈ F m := by
      intro m hm
      induction m, hm using Int.leInduction with
      | base => exact h1
      | succ m hm ih => exact up x hx.1 m (by omega) ih
    have h0 : ∀ lam, ctr lam x = 0 := fun lam => ((PP l).PD K).Fil_sep _ fun a =>
      (hF _ _).1 (hanti (le_max_left a 1) (key _ (le_max_right _ _) lam))
    rw [Submodule.mem_bot, eq_sum x]
    simp [h0]

end UpperTheory.V.Loc.CrUnipChar

open UpperTheory.V.Loc.CrUnipChar in
theorem UpperTheory.V.Loc.crUnipChar :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] [Module.Finite ℚ_[l] A] [TopologicalSpace A] [IsModuleTopology ℚ_[l] A] [IsTopologicalRing A] (κ : G →* Aˣ), Continuous (fun g => (κ g : A)) → (∀ g, IsNilpotent ((κ g : A) - 1)) → ∀ H : Subgroup G, IsOpen (H : Set G) → CrOn φ (chRep κ) H → ∀ g, φ g ∈ Iq l → κ g = 1 := by
  intro l _ G _ _ _ φ hφ A _ _ _ _ _ _ κ hc hκ H hH hcr g hg
  have hφ' : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  obtain ⟨K, -, -, -, -, hK, hi, -⟩ := openField (φ.comp H.subtype) hφ'
  haveI := K.2
  obtain ⟨f0, f1⟩ := fil (φ.comp H.subtype) K hK (κ.comp H.subtype) fun h => hκ h
  have hca : ReciprocityTheory.Gal.ContAction (chRep (κ.comp H.subtype)) := by
    unfold ReciprocityTheory.Gal.ContAction
    exact ((hc.comp continuous_subtype_val).comp continuous_fst).mul continuous_snd
  have hw := crWt0 (φ.comp H.subtype) hφ' (chRep (κ.comp H.subtype)) hca hcr f0 f1
  obtain ⟨n, hn, -, h, hh⟩ := (φ.comp H.subtype).range.exists_pow_mem_of_index_ne_zero
    (by rw [hi]; exact finrank_pos.ne') (φ g)
  have e : (h : G) = g ^ n := hφ.injective (by rw [map_pow]; exact hh)
  have h1 := LinearMap.congr_fun (hw h (by rw [hh]; exact (Iq l).pow_mem hg n)) 1
  have h2 : (κ g : A) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← e]
    simpa [chRep] using h1
  exact Units.ext (eq_one_of_pow (Q := ℚ_[l]) (hκ g) hn.ne' h2)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsAlgebraicVectorSpanningSubspace
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

section
open GlobalTheory.UnramifiedCrys GlobalTheory.Cyc
open scoped Topology

private def algSub (p : ℕ) [hp : Fact p.Prime] (R : Type) [CommRing R] [CharP R p] : Subring R where
  carrier := {y | ∃ m, 0 < m ∧ y ^ p ^ m = y}
  one_mem' := ⟨1, one_pos, one_pow _⟩
  zero_mem' := ⟨1, one_pos, zero_pow (pow_pos hp.out.pos _).ne'⟩
  mul_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [mul_pow, pow_pow_mul hx, mul_comm a b, pow_pow_mul hy]
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [add_pow_char_pow, pow_pow_mul hx, mul_comm a b, pow_pow_mul hy]
  neg_mem' := by
    rintro x ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    have h := sub_pow_char_pow (p := p) (n := a) (0 : R) x
    rwa [zero_sub, hx, zero_pow (pow_pos hp.out.pos _).ne', zero_sub] at h

private theorem exists_alg {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] {R : Type} [CommRing R]
    (ρ : G →* (R ≃+* R)) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [CharP R p]
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (hM : Continuous M)
    (hJ : ∀ g, (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → ρ g y = y) → M g = 1) :
    ∃ W : Matrix (Fin r) (Fin r) (WittVector p R), IsUnit W.det ∧
      (∀ g, (M g).map (zlW p R) * W.map (WittVector.map (ρ g).toRingHom) = W) ∧
      ∀ i j n, ∃ m, 0 < m ∧ (W i j).coeff n ^ p ^ m = (W i j).coeff n :=
  _root_.UpperTheory.Reformulated.B.RestrictAutomorphism.exists_alg ρ hopen M hM hJ

end

theorem UpperTheory.exists_algebraic_vector_spanning_subspace :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) {r : ℕ} (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ℤ_[l]), Continuous M → (∀ g ∈ IK K, M g = 1) → ∃ W : Matrix (Fin r) (Fin r) (Ainf l), IsUnit W.det ∧ (∀ g, (M g).map (zlW l (OCb l)) * W.map (AI.actW (g : GQ l)) = W) ∧ ∀ i j n, ∃ m, 0 < m ∧ (W i j).coeff n ^ l ^ m = (W i j).coeff n := by
  intro l _ P AI K r M hM hI
  have := GlobalTheory.UnramifiedCrys.compactSpace_GK K
  exact exists_alg (p := l) (AI.actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (GlobalTheory.UnramifiedCrys.eventually_actT_eq AI y m hm hy)) M hM
    (fun g hg => hI g (Subgroup.subset_closure fun x hx =>
      GlobalTheory.UnramifiedCrys.norm_sub_lt_one_of_fix AI g hg x hx))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArith
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

private theorem cyc_continuous (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  _root_.UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cyc_continuous F Ω l

theorem UpperTheory.V.Loc.laArith :
    GlobalArtinReciprocity → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous κ → ∀ (m : ℤ) (k : ℕ), 0 < k → (∀ g : ↥(Dec (F := F) A), (g : G F Ω) ∈ Ine (F := F) A → (κ g * cycBar F Ω l g ^ (-m)) ^ k = 1) → IsLocAlg h κ fun _ => -m := by
  intro H F Ω _ _ _ _ _ l _ A w h hl κ hκ m k hk hpow
  set c : ↥(Dec (F := F) A) →* (Qbar l)ˣ := (cycBar F Ω l).comp (Dec (F := F) A).subtype with hc
  have hcc : Continuous c := (cyc_continuous F Ω l).comp continuous_subtype_val
  let i : ↥(Ine (F := F) A) →* ↥(Dec (F := F) A) := (Subgroup.inclusion (Weil_le_Dec h)).comp (ineIncl h)
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  let χ : ↥(Dec (F := F) A) →* (Qbar l)ˣ := κ * c ^ (-m)
  have hχ : Continuous χ := hκ.mul ((continuous_zpow (-m)).comp hcc)
  have ho : IsOpen ((χ.comp i)⁻¹.ker : Set ↥(Ine (F := F) A)) := by
    refine isOpen_ker_of_pow _ (hχ.comp hi).inv hk fun σ => ?_
    have h1 : χ (i σ) ^ k = 1 := hpow (i σ) σ.2
    rw [MonoidHom.inv_apply, MonoidHom.comp_apply, inv_pow, h1, inv_one]
  obtain ⟨hmul, hz, h0⟩ := UpperTheory.V.Loc.laMul (l := l) h
  have H0 : IsWtPart h χ 0 (χ.comp i)⁻¹ := h0 χ _ ho fun σ => mul_inv_cancel _
  have H1 := (hmul _ _ _ _ _ _ H0 (hz _ _ _ m (UpperTheory.V.Loc.laCyc H h hl))).1
  have e : χ * c ^ m = κ := by
    simp only [χ, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have e' : (0 + m • fun _ : Emb l w => (-1 : ℤ)) = fun _ => -m := by
    funext τ
    simp
  rw [← hc, e, e'] at H1
  exact ⟨_, H1⟩
end

