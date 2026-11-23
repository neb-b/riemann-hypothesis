module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0031

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.IsPtOf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

section SlopeTestRemainingChoices

variable {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] [IsNoetherianRing R]
  [NormedField K] [IsUltrametricDist K] [Algebra O K]

omit [IsNoetherianRing R] [IsUltrametricDist K] in
private theorem ipo_mul {f : R →ₐ[O] K} (hf : IsLocPt f) (x : R) {z : R} (hz : z ∈ maximalIdeal R) :
    ‖f (x * z)‖ ≤ ‖f z‖ := by
  rw [map_mul, norm_mul]
  rcases eq_or_ne (f z) 0 with h0 | h0
  · simp [h0]
  have hpos : 0 < ‖f z‖ := norm_pos_iff.mpr h0
  suffices hx : ‖f x‖ ≤ 1 by nlinarith [norm_nonneg (f x)]
  by_contra hx
  push_neg at hx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖f z‖⁻¹) hx
  have hmem : x ^ n * z ∈ maximalIdeal R := Ideal.mul_mem_left _ _ hz
  have h1 := hf _ hmem
  rw [map_mul, map_pow, norm_mul, norm_pow] at h1
  have := (inv_lt_iff_one_lt_mul₀ hpos).mp hn
  linarith [mul_comm (‖f x‖ ^ n) ‖f z‖]

private theorem ipo_rho {f : R →ₐ[O] K} (hf : IsLocPt f) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ z ∈ maximalIdeal R, ‖f z‖ ≤ ρ := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal R) : (maximalIdeal R).FG)
  refine ⟨((s.sup fun g => ‖f g‖₊ : NNReal) : ℝ), NNReal.coe_nonneg _, ?_, ?_⟩
  · have : (s.sup fun g => ‖f g‖₊) < 1 := by
      rw [Finset.sup_lt_iff (by simp)]
      intro g hg
      have hgm : g ∈ maximalIdeal R := hs ▸ Ideal.subset_span hg
      have := hf g hgm
      exact_mod_cast this
    exact_mod_cast this
  · intro z hz
    rw [← hs] at hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      have : ‖f x‖₊ ≤ s.sup fun g => ‖f g‖₊ := Finset.le_sup (f := fun g => ‖f g‖₊) hx
      exact_mod_cast this
    | zero => simp
    | add x y hx hy ihx ihy =>
      rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ihx ihy)
    | smul a x hx ihx =>
      rw [smul_eq_mul]
      refine (ipo_mul hf a ?_).trans ihx
      exact hs ▸ hx

private theorem ipo_pow {f : R →ₐ[O] K} (hf : IsLocPt f) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ z ∈ maximalIdeal R ^ n, ‖f z‖ < ε := by
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := ipo_rho hf
  have key : ∀ n : ℕ, ∀ z ∈ maximalIdeal R ^ (n + 1), ‖f z‖ ≤ ρ ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro z hz
      rw [zero_add, pow_one] at hz ⊢
      exact hρ z hz
    | succ n ih =>
      intro z hz
      rw [pow_succ] at hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro a ha b hb
        rw [map_mul, norm_mul, pow_succ]
        exact mul_le_mul (ih a ha) (hρ b hb) (norm_nonneg _) (pow_nonneg hρ0 _)
      · intro x y hx hy
        rw [map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hρ1
  refine ⟨n + 1, fun z hz => (key n z hz).trans_lt ?_⟩
  calc ρ ^ (n + 1) ≤ ρ ^ n := pow_le_pow_of_le_one hρ0 hρ1.le (Nat.le_succ n)
    _ < ε := hn

private theorem ipo_cont {f : R →ₐ[O] K} (hf : IsLocPt f) {X : Type} [TopologicalSpace X] (u : X → R)
    (hu : AdicCont (maximalIdeal R) u) : Continuous fun g => f (u g) := by
  rw [continuous_iff_continuousAt]
  intro g
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := ipo_pow hf hε
  have hopen := (hu n).isOpen_fiber (Ideal.Quotient.mk (maximalIdeal R ^ n) (u g))
  filter_upwards [hopen.mem_nhds rfl] with g' hg'
  have heq : Ideal.Quotient.mk (maximalIdeal R ^ n) (u g') = Ideal.Quotient.mk (maximalIdeal R ^ n) (u g) := hg'
  rw [Ideal.Quotient.eq] at heq
  rw [dist_eq_norm, ← map_sub]
  exact hn _ heq

end SlopeTestRemainingChoices

private theorem ipo_le_one {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R]
    {f : R →ₐ[c.O] PadicAlgCl l} (hf : IsLocPt f) (x : R) : ‖f x‖ ≤ 1 := by
  haveI := c.dvr
  haveI : IsLocalHom (algebraMap c.O R) := IsCO.isLocalHom
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hm : algebraMap c.O R ϖ ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hϖ.not_isUnit ((isUnit_map_iff (algebraMap c.O R) ϖ).mp hu)
  have hne : f (algebraMap c.O R ϖ) ≠ 0 := by
    rw [AlgHom.commutes]
    intro h
    apply hϖ.ne_zero
    exact Subtype.ext (by simpa using h)
  have hpos : 0 < ‖f (algebraMap c.O R ϖ)‖ := norm_pos_iff.mpr hne
  have h := ipo_mul hf x hm
  rw [map_mul, norm_mul] at h
  nlinarith [norm_nonneg (f x)]

private theorem diagonal_rep_map_entries {G A B : Type} [Group G] [CommRing A] [CommRing B] (φ : A →+* B) (η : G →* ℤˣ) (Ψ : G →* Aˣ)
    (g : G) (a b : Fin 3) :
    (r0 η ((Units.map φ.toMonoidHom).comp Ψ) g).mat a b = φ ((r0 η Ψ g).mat a b) := by
  simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply, MonoidHom.comp_apply]
  split_ifs
  · first
      | (rw [← map_zpow, Units.coe_map]; rfl)
      | (rw [← map_pow, Units.coe_map]; rfl)
  · simp

theorem UpperTheory.V.U3.isPt_push :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁),
      ∀ f : S.R →ₐ[c.O] PadicAlgCl l, IsLocPt f → D.IsPt U g₁ (push f S.r.hom) := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ _ S f hf
  have hid : S.r.map (AlgHom.id c.O S.R) = S.r := GLift.ext rfl
  have h0 := (S.rep S.R).1 (AlgHom.id c.O S.R)
  rw [hid] at h0
  obtain ⟨hn, hk, φ, hφ, hI⟩ := h0
  have hm : ∀ g a b, (push f S.r.hom g).mat a b = f ((S.r.hom g).mat a b) := fun _ _ _ => rfl
  refine ⟨fun g => S.r.hasMult g, ?_, fun g a b => ipo_le_one hf _, fun g a b => ?_, ⟨?_, ?_, ?_⟩, fun g hg => ?_,
    f.comp φ, fun x hx => hf _ ?_, fun x hx => ?_, ?_⟩
  · exact continuous_matrix fun a b => ipo_cont hf _ (S.r.cont a b)
  · have h1 : (r0 D.η D.ΨQ g).mat a b = algebraMap c.O (PadicAlgCl l) ((r0 D.η D.Ψ g).mat a b) :=
      diagonal_rep_map_entries _ _ _ _ _ _
    rw [hm, h1, ← f.commutes, ← map_sub]
    refine hf _ ((res_eq_zero_iff c.O S.R _).1 ?_)
    have h2 : res c.O S.R ((S.r.hom g).mat a b) = (rbar c.O D.η D.Ψ g).mat a b :=
      congrArg (fun x : GG (m := 3) (R := ResidueField c.O) => x.mat a b) (S.r.red g)
    have h3 : (rbar c.O D.η D.Ψ g).mat a b = residue c.O ((r0 D.η D.Ψ g).mat a b) := diagonal_rep_map_entries _ _ _ _ _ _
    rw [map_sub, AlgHom.commutes, h2, h3]
    exact sub_self _
  · show (S.r.hom D.cc).mat.map (f : S.R →+* PadicAlgCl l) = 1
    rw [hn.atc, Matrix.map_one _ (map_zero _) (map_one _)]
  · have := congrArg f hn.z12
    rw [map_zero, zmat, Matrix.sub_apply, map_sub] at this
    exact this
  · have := congrArg f hn.z21
    rw [map_zero, zmat, Matrix.sub_apply, map_sub] at this
    exact this
  · show GG.map (f : S.R →+* PadicAlgCl l) (S.r.hom g) = 1
    rw [hk g hg, map_one]
  · show φ x ∈ maximalIdeal S.R
    rw [← res_eq_zero_iff c.O, res_map, res_eq_zero_iff]
    exact hx
  · have : φ x = 0 := hI hx
    show f (φ x) = 0
    rw [this, map_zero]
  · have h1 : (U.r.map φ).hom = S.r.hom.comp D.ι := congrArg GLift.hom hφ
    refine MonoidHom.ext fun g => ?_
    show GG.map (f : S.R →+* PadicAlgCl l) ((U.r.map φ).hom g) = _
    rw [h1]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.LocalEulerCharacteristicOfPrimeNotMem
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

section Transport

variable {R R' Γ Γ' M : Type} [CommRing R] [CommRing R'] [Group Γ] [TopologicalSpace Γ] [Group Γ']
  [TopologicalSpace Γ'] [AddCommGroup M] [Module R M] [Module R' M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation R Γ M) (ρ' : Representation R' Γ' M) (e : Γ' ≃* Γ) (he : Continuous e)
  (he' : Continuous e.symm) (h : ∀ g m, ρ' g m = ρ (e g) m)

include h in
private theorem invariants_equiv : Nonempty (H0 ρ ≃ H0 ρ') := by
  refine ⟨Equiv.subtypeEquivRight fun m => ?_⟩
  rw [mem_riemannRochSpace_iff_regularAt_everywhere, mem_riemannRochSpace_iff_regularAt_everywhere]
  constructor
  · intro H g
    rw [h]
    exact H _
  · intro H g
    have := H (e.symm g)
    rwa [h, e.apply_symm_apply] at this

include he he' h in
private theorem first_cohomology_equiv : Nonempty (H1 ρ ≃ H1 ρ') := by
  have key : ∀ f : Γ → M, f ∈ Z1 ρ ↔ (fun g => f (e g)) ∈ Z1 ρ' := by
    intro f
    show (Continuous f ∧ _) ↔ (Continuous _ ∧ _)
    constructor
    · rintro ⟨hc, hf⟩
      refine ⟨hc.comp he, fun a b => ?_⟩
      simp only [map_mul, h]
      exact hf _ _
    · rintro ⟨hc, hf⟩
      refine ⟨?_, fun a b => ?_⟩
      · have := hc.comp he'
        convert this using 1
        funext g
        simp
      · have := hf (e.symm a) (e.symm b)
        simpa [map_mul, h] using this
  have keyB : ∀ f : Γ → M, f ∈ B1 ρ ↔ (fun g => f (e g)) ∈ B1 ρ' := by
    intro f
    rw [mem_coboundaries1, mem_coboundaries1]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, fun g => by simp [hm, h]⟩
    · rintro ⟨m, hm⟩
      refine ⟨m, fun g => ?_⟩
      have := hm (e.symm g)
      simpa [h] using this
  let φ : Z1 ρ ≃ Z1 ρ' :=
    { toFun := fun f => ⟨fun g => f.1 (e g), (key f.1).1 f.2⟩
      invFun := fun f => ⟨fun g => f.1 (e.symm g), (key _).2 (by
        rw [show (fun g => f.1 (e.symm (e g))) = f.1 from funext fun g => by simp]
        exact f.2)⟩
      left_inv := fun f => Subtype.ext (funext fun g => by simp)
      right_inv := fun f => Subtype.ext (funext fun g => by simp) }
  refine ⟨Quotient.congr φ fun a b => ?_⟩
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap]
  exact keyB _

include he he' h in
private theorem second_cohomology_equiv : Nonempty (H2 ρ ≃ H2 ρ') := by
  have key : ∀ f : Γ × Γ → M, f ∈ Z2 ρ ↔ (fun p => f (e p.1, e p.2)) ∈ Z2 ρ' := by
    intro f
    show (Continuous f ∧ _) ↔ (Continuous _ ∧ _)
    constructor
    · rintro ⟨hc, hf⟩
      refine ⟨hc.comp (he.prodMap he), fun a b c => ?_⟩
      simp only [map_mul, h]
      exact hf _ _ _
    · rintro ⟨hc, hf⟩
      refine ⟨?_, fun a b c => ?_⟩
      · have := hc.comp (he'.prodMap he')
        convert this using 1
        funext p
        simp
      · have := hf (e.symm a) (e.symm b) (e.symm c)
        simpa [map_mul, h] using this
  have keyB : ∀ f : Γ × Γ → M, f ∈ B2 ρ ↔ (fun p => f (e p.1, e p.2)) ∈ B2 ρ' := by
    intro f
    rw [separated_dvr_second_cohomology_mem, separated_dvr_second_cohomology_mem]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun g => c (e g), hc.comp he, ?_⟩
      funext ⟨a, b⟩
      simp [d1_apply, h, map_mul]
    · rintro ⟨c, hc, hcf⟩
      refine ⟨fun g => c (e.symm g), hc.comp he', ?_⟩
      funext ⟨a, b⟩
      have := congrFun hcf (e.symm a, e.symm b)
      rw [d1_apply] at this
      rw [d1_apply]
      simpa [h, map_mul] using this
  let φ : Z2 ρ ≃ Z2 ρ' :=
    { toFun := fun f => ⟨fun p => f.1 (e p.1, e p.2), (key f.1).1 f.2⟩
      invFun := fun f => ⟨fun p => f.1 (e.symm p.1, e.symm p.2), (key _).2 (by
        rw [show (fun p : Γ' × Γ' => f.1 (e.symm (e p.1), e.symm (e p.2))) = f.1 from
          funext fun p => by simp]
        exact f.2)⟩
      left_inv := fun f => Subtype.ext (funext fun p => by simp)
      right_inv := fun f => Subtype.ext (funext fun p => by simp) }
  refine ⟨Quotient.congr φ fun a b => ?_⟩
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap, Submodule.mem_comap]
  exact keyB _

end Transport

private def resC (R : Type) {k Γ M : Type} [CommRing R] [CommRing k] [Algebra R k] [Group Γ] [AddCommGroup M]
    [Module R M] [Module k M] [IsScalarTower R k M] (ρ : Representation k Γ M) : Representation R Γ M where
  toFun g := (ρ g).restrictScalars R
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem UpperTheory.local_euler_characteristic_of_prime_not_mem :
    LocalFiniteness → LocalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v → ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal →
          ∀ ρ : Representation k (Dec (F := ℚ) A) M, ContAction ρ →
          Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ Module.finrank k (H1 ρ) = Module.finrank k (H0 ρ) + Module.finrank k (H2 ρ) := by
  intro hfin hec Ω _ _ _ l _ k M _ _ _ _ _ _ _ _ _ _ A v hv hl ρ hc
  haveI : Finite M := Module.finite_of_finite k
  haveI : CharP k (l ^ 1) := by rw [pow_one]; infer_instance
  letI : Algebra (ZMod (l ^ 1)) k := ZMod.algebra k (l ^ 1)
  letI : Module (ZMod (l ^ 1)) M := Module.compHom M (algebraMap (ZMod (l ^ 1)) k)
  haveI : IsScalarTower (ZMod (l ^ 1)) k M := ⟨fun a b m => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let ρ₀ := resC (ZMod (l ^ 1)) ρ
  have hc₀ : ContAction ρ₀ := hc
  obtain ⟨-, hF1, hF2, -⟩ := hfin ℚ Ω l 1 M A ρ₀ v one_pos hv hc₀
  have hE := (hec ℚ Ω l 1 M A ρ₀ v one_pos hv hc₀).2 hl
  have hr : ∀ g m, ρ g m = ρ₀ (MulEquiv.refl _ g) m := fun _ _ => rfl
  obtain ⟨e0⟩ := invariants_equiv ρ₀ ρ (MulEquiv.refl _) hr
  obtain ⟨e1⟩ := first_cohomology_equiv ρ₀ ρ (MulEquiv.refl _) continuous_id continuous_id hr
  obtain ⟨e2⟩ := second_cohomology_equiv ρ₀ ρ (MulEquiv.refl _) continuous_id continuous_id hr
  haveI : Finite (H1 ρ) := Finite.of_equiv _ e1
  haveI : Finite (H2 ρ) := Finite.of_equiv _ e2
  refine ⟨Module.Finite.of_finite, Module.Finite.of_finite, ?_⟩
  have hcard : Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) := by
    rw [← Nat.card_congr e1, ← Nat.card_congr e0, ← Nat.card_congr e2]
    exact hE
  have pw : ∀ (V : Type) [AddCommGroup V] [Module k V] [Finite V],
      Nat.card V = Nat.card k ^ Module.finrank k V := by
    intro V _ _ _
    haveI := Fintype.ofFinite V
    haveI := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  rw [pw (H1 ρ), pw (H0 ρ), pw (H2 ρ), ← pow_add] at hcard
  exact Nat.pow_right_injective Finite.one_lt_card hcard
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.OrbEquiv
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem isCM (K : Type) [Field K] [NumberField K] (h : Module.finrank ℚ K = 2) (h' : IsTotallyComplex K) :
    IsCMField K := by
  haveI : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := h }
  exact IsCMField.ofCMExtension ℚ K

private theorem exists_w (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ w.asIdeal :=
  _root_.UpperTheory.Reformulated.B.Qk10.exists_w K hp

private theorem cop_norm {K : Type} [Field K] [NumberField K] {p N : ℕ} (hp : p.Prime) (hN : ¬ p ∣ N)
    {w : HeightOneSpectrum (𝓞 K)} (hw : (p : 𝓞 K) ∈ w.asIdeal) : (normV w).Coprime N := by
  have h := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
  rw [Ideal.absNorm_span_natCast] at h
  rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] at *
  exact Nat.Coprime.coprime_dvd_left h (((Nat.Prime.coprime_iff_not_dvd hp).2 hN).pow_left _)

private theorem frob_val {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Field K] [NumberField K] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [hl : Fact l.Prime] {p N : ℕ} [NeZero N] (hp : p.Prime) (hN : ¬ p ∣ N) (hlp : l ≠ p)
    {w : HeightOneSpectrum (𝓞 K)} (hw : (p : 𝓞 K) ∈ w.asIdeal) {B : ValuationSubring Ω} (hB : IsPlaceOver B w)
    {σ : G K Ω} (hσ : IsFrob B (normV w) σ) :
    ((Chr.cls ℚ Ω N (galEmb ℚ K Ω σ) : (ZMod N)ˣ) : ZMod N) = normV w ∧
      ((cycZ ℚ Ω l (galEmb ℚ K Ω σ) : ℤ_[l]ˣ) : ℤ_[l]) = normV w := by
  obtain ⟨-, -, -, hcop, -, -, hpow, -⟩ := ML.placeBasic Ω
  have hp' : ML.Over B p := by
    have := (hB p).2 hw
    simpa using this
  constructor
  · have hφ : IsFrob (F := ℚ) B (normV w) (galEmb ℚ K Ω σ) :=
      ⟨Subgroup.mem_comap.1 (((galEmbFam ℚ K Ω l).1 B).1.ge hσ.1), hσ.2⟩
    have h := hpow B _ N _ hφ (hcop B p N ((Nat.Prime.coprime_iff_not_dvd hp).2 hN) hp')
    rw [(Chr.clsFacts ℚ Ω N).2.2.1 _ (ZMod.unitOfCoprime _ (cop_norm hp hN hw)) fun ζ hζ => ?_, ZMod.coe_unitOfCoprime]
    rw [h ζ hζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ]
  · refine cycZ_of_isFrob (F := K) (fun h => ?_) hB hσ
    refine hcop B p l ((Nat.coprime_primes hp hl.out).2 hlp.symm) hp' ?_
    have := (hB l).2 h
    simpa using this

private theorem vl_bound {l : ℕ} [hl : Fact l.Prime] {ι : Type} {κ : Type} [Fintype ι] (X : ι → Finset κ)
    (f : ι → κ → PadicAlgCl l) (NN : ℤ) (h0 : NN ≠ 0) (hf : ∀ o, ∀ ρ ∈ X o, f o ρ ≠ 0)
    (h : ‖((NN : ℤ) : PadicAlgCl l)‖ ≤ ∏ o, ∏ ρ ∈ X o, ‖f o ρ‖) :
    ∑ o, ∑ ρ ∈ X o, vl l (f o ρ) ≤ padicValInt l NN := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have e1 : ‖((NN : ℤ) : PadicAlgCl l)‖ = (l : ℝ) ^ (-(padicValInt l NN : ℝ)) := by
    rw [← map_intCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends,
      Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast h0), Padic.valuation_intCast, ← Real.rpow_intCast]
    simp
  have h2 := Real.logb_le_logb_of_le hl1 (by rw [e1]; positivity) h
  rw [e1, Real.logb_rpow (by positivity) hl1.ne', Real.logb_prod _ _ fun o _ =>
    Finset.prod_ne_zero_iff.2 fun ρ hρ => norm_ne_zero_iff.2 (hf o ρ hρ),
    Finset.sum_congr rfl fun o _ => Real.logb_prod _ _ fun ρ hρ => norm_ne_zero_iff.2 (hf o ρ hρ)] at h2
  simp only [vl, Finset.sum_neg_distrib]
  linarith

private theorem ker_comp {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O') (hf : Function.Injective f)
    (ψ : DirichletCharacter O N) : (ψ.ringHomComp f).toUnitHom.ker = ψ.toUnitHom.ker := by
  ext u
  simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, MulChar.ringHomComp_apply, Units.val_one]
  exact map_eq_one_iff f hf

private theorem card_orb {N : ℕ} [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    Nat.card {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H} ≤ Nat.totient H.index := by
  by_cases h : ∃ χ : DirichletCharacter ℂ N, χ.toUnitHom.ker = H
  · obtain ⟨χ, rfl⟩ := h
    obtain ⟨h1, -, -, h2⟩ := orbFacts ℂ N χ
    rw [h1, ← h2]
    exact le_rfl
  · haveI : IsEmpty {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H} := ⟨fun x => h ⟨x.1, x.2⟩⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

private theorem t_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] (c : Coef l)
    {N : ℕ} [NeZero N] (e q : ℕ) (ψ : DirichletCharacter c.O N) (ι : Qbar l ≃+* ℂ) (g : G ℚ Ω)
    (h1 : ((Chr.cls ℚ Ω N g : (ZMod N)ˣ) : ZMod N) = q) (h2 : ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = q) :
    ι.symm (Af.eis3 q e (ι (algebraMap c.O (PadicAlgCl l) (ψ q)))⁻¹) =
      algebraMap c.O (PadicAlgCl l) ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) g⁻¹ : c.O) + 1 +
      (((Chr.Psi l e (Chr.dirG ℚ Ω ψ) g⁻¹)⁻¹ : c.Oˣ) : c.O)) := by
  have e1 : ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) g : c.Oˣ) : c.O) = (q : c.O) ^ e * ψ q := by
    simp [Chr.Psi, Chr.dirG, chiO, h1, h2]
  rw [map_inv (Chr.Psi l e (Chr.dirG ℚ Ω ψ)), inv_inv, map_add (f := _), map_add (f := _), map_one, map_units_inv, e1]
  simp [Af.eis3, mul_comm]

private theorem comp_inj {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O') (hf : Function.Injective f)
    {ψ ψ' : DirichletCharacter O N} (h : ψ.ringHomComp f = ψ'.ringHomComp f) : ψ = ψ' :=
  MulChar.ext' fun a => hf (by rw [← MulChar.ringHomComp_apply, h, MulChar.ringHomComp_apply])

private theorem orb_equiv {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (H : Subgroup (ZMod N)ˣ) (f : c.O →+* ℂ)
    (hf : Function.Injective f) {ψ₀ : DirichletCharacter c.O N} (h₀ : ψ₀ ∈ orb c H) :
    ∃ E : orb c H ≃ {χ : DirichletCharacter ℂ N // χ.toUnitHom.ker = H}, ∀ ψ, (E ψ).1 = ψ.1.ringHomComp f := by
  refine ⟨Equiv.ofBijective (fun ψ => ⟨ψ.1.ringHomComp f, (ker_comp f hf _).trans ((mem_orb c).1 ψ.2)⟩) ⟨?_, ?_⟩,
    fun _ => rfl⟩
  · intro a b h
    exact Subtype.ext (comp_inj f hf (congrArg Subtype.val h))
  · rintro ⟨χ, hχ⟩
    have h1 := (ker_comp f hf ψ₀).trans ((mem_orb c).1 h₀)
    obtain ⟨j, -, hj⟩ := ((orbFacts ℂ N (ψ₀.ringHomComp f)).2.2.1 χ).1 (hχ.trans h1.symm)
    rw [MulChar.ringHomComp_pow] at hj
    refine ⟨⟨ψ₀ ^ j, (mem_orb c).2 ?_⟩, Subtype.ext hj.symm⟩
    rw [← ker_comp f hf, ← hj, hχ]
end

