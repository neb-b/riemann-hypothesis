module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.Fv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CtrlDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsLatticeIffFixedPointQuadraticTorus
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

private theorem im_form {K : Type} [Field K] {τ : K} (x y : Etau K τ) :
    (x * star y).im = x.im * y.re - x.re * y.im := by
  simp; ring

private theorem smul_im' {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K} (r : O)
    (x : Etau K τ) : (r • x).im = algebraMap O K r * x.im := by
  rw [QuadraticAlgebra.im_smul, Algebra.smul_def]

private theorem smul_re' {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K} (r : O)
    (x : Etau K τ) : (r • x).re = algebraMap O K r * x.re := by
  rw [QuadraticAlgebra.re_smul, Algebra.smul_def]

private theorem fix_lat {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {τ t : K} {S : Set (Etau K τ)} (h : IsFixP O τ t S) : IsLat O τ S := by
  classical
  obtain ⟨s, hs⟩ := h.fg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
    (s.image (fun x : Etau K τ => t * x.im) ∪ s.image (fun x : Etau K τ => t * x.re))
  set B : K := algebraMap O K (b : O) with hBdef
  have hB : B ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have key : ∀ x ∈ Submodule.span O (s : Set (Etau K τ)),
      t * x.im * B ∈ (algebraMap O K).range ∧ t * x.re * B ∈ (algebraMap O K).range := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r1, hr1⟩ := hb (t * x.im) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))
      obtain ⟨r2, hr2⟩ := hb (t * x.re) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx))
      refine ⟨⟨r1, ?_⟩, ⟨r2, ?_⟩⟩
      · rw [hr1, Algebra.smul_def, hBdef]
        ring
      · rw [hr2, Algebra.smul_def, hBdef]
        ring
    | zero => simp
    | add x y _ _ hx hy =>
      refine ⟨?_, ?_⟩
      · have e := add_mem hx.1 hy.1
        convert e using 1
        simp only [QuadraticAlgebra.im_add]
        ring
      · have e := add_mem hx.2 hy.2
        convert e using 1
        simp only [QuadraticAlgebra.re_add]
        ring
    | smul r x _ hx =>
      rw [smul_im', smul_re']
      refine ⟨?_, ?_⟩
      · have e := mul_mem (RingHom.mem_range_self (algebraMap O K) r) hx.1
        convert e using 1
        ring
      · have e := mul_mem (RingHom.mem_range_self (algebraMap O K) r) hx.2
        convert e using 1
        ring
  have m1 : B • (1 : Etau K τ) ∈ S := by
    rw [h.dual]
    intro x hx
    rw [hs] at hx
    have e : (x * star (B • (1 : Etau K τ))).im = x.im * B := by
      rw [im_form]
      simp
    rw [e, ← mul_assoc]
    exact (key x hx).1
  have m2 : B • (ω : Etau K τ) ∈ S := by
    rw [h.dual]
    intro x hx
    rw [hs] at hx
    have e : (x * star (B • (ω : Etau K τ))).im = -(x.re * B) := by
      rw [im_form]
      simp
    rw [e, mul_neg, ← mul_assoc]
    exact neg_mem (key x hx).2
  refine ⟨h.fg, ?_⟩
  rw [eq_top_iff]
  intro y _
  have e : y = (y.re / B) • (B • (1 : Etau K τ)) + (y.im / B) • (B • (ω : Etau K τ)) := by
    ext <;> simp <;> field_simp
  rw [e]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span m1))
    (Submodule.smul_mem _ _ (Submodule.subset_span m2))

private theorem dual_pair {O K : Type} [CommRing O] [Field K] [Algebra O K]
    {τ : K} (u v : Etau K τ) (hd : u.im * v.re - u.re * v.im ≠ 0) (y : Etau K τ) :
    y ∈ (Submodule.span O {u, v} : Submodule O (Etau K τ)) ↔
      ∀ x ∈ (Submodule.span O {u, v} : Submodule O (Etau K τ)),
        (u.im * v.re - u.re * v.im)⁻¹ * (x * star y).im ∈ (algebraMap O K).range := by
  constructor
  · intro hy x hx
    obtain ⟨r, s, rfl⟩ := Submodule.mem_span_pair.1 hy
    obtain ⟨p, q, rfl⟩ := Submodule.mem_span_pair.1 hx
    refine ⟨p * s - q * r, ?_⟩
    rw [im_form]
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, smul_im', smul_re',
      map_sub, map_mul]
    field_simp
    ring
  · intro H
    obtain ⟨β, hβ⟩ := H u (Submodule.subset_span (by simp))
    obtain ⟨α, hα⟩ := H v (Submodule.subset_span (by simp))
    rw [im_form] at hα hβ
    refine Submodule.mem_span_pair.2 ⟨-α, β, ?_⟩
    ext
    · simp only [QuadraticAlgebra.re_add, smul_re', map_neg, hα, hβ]
      field_simp
      ring
    · simp only [QuadraticAlgebra.im_add, smul_im', map_neg, hα, hβ]
      field_simp
      ring

theorem UpperTheory.isLattice_iff_fixedPoint_quadraticTorus :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ S : Set (Etau K τ), (∀ t : K, IsFixP O τ t S → IsLat O τ S) ∧ (IsLat O τ S → (∀ y ∈ S, ω * y ∈ S) → ∃ t : K, t ≠ 0 ∧ IsFixP O τ t S) := by
  intro O K _ _ _ _ _ Δ τ hL hτ S
  haveI := hL.frac
  refine ⟨fun t h => fix_lat h, fun hS hst => ?_⟩
  obtain ⟨y, x, hx, -, -, e⟩ := latCls O K Δ τ hL hτ S hS
  have e' : S = (Submodule.span O {(y : Etau K τ), (y : Etau K τ) * x} : Submodule O (Etau K τ)) := by
    rw [e]
    ext w
    simp only [SetLike.mem_coe, Submodule.mem_span_pair, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨p, q, rfl⟩, rfl⟩
      exact ⟨p, q, by simp [mul_add]⟩
    · rintro ⟨p, q, rfl⟩
      exact ⟨_, ⟨p, q, rfl⟩, by simp [mul_add]⟩
  have hn : QuadraticAlgebra.norm (y : Etau K τ) ≠ 0 := (isUnit_iff_norm_isUnit.1 y.isUnit).ne_zero
  have hd : (y : Etau K τ).im * ((y : Etau K τ) * x).re - (y : Etau K τ).re * ((y : Etau K τ) * x).im ≠ 0 := by
    have : (y : Etau K τ).im * ((y : Etau K τ) * x).re - (y : Etau K τ).re * ((y : Etau K τ) * x).im =
        -(QuadraticAlgebra.norm (y : Etau K τ) * x.im) := by
      simp [norm_def]; ring
    rw [this]
    exact neg_ne_zero.2 (mul_ne_zero hn hx)
  refine ⟨_, inv_ne_zero hd, hS.fg, fun w => ?_, hst⟩
  rw [e']
  exact dual_pair _ _ hd w
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemLatticeOfValuesAtDoubleCosetReps
section
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem detd_mulVec {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {n : ℕ} (L : Submodule O Ω)
    (M : Matrix (Fin n) (Fin n) Ω) (hM : ∀ i j, M i j ∈ (algebraMap O Ω).range) (v : Fin n → Ω)
    (hv : ∀ k, v k ∈ L) (k : Fin n) : (M *ᵥ v) k ∈ L := by
  rw [Matrix.mulVec, dotProduct]
  refine Submodule.sum_mem L fun j _ => ?_
  obtain ⟨r, hr⟩ := hM k j
  rw [← hr, ← Algebra.smul_def]
  exact L.smul_mem r (hv j)

theorem UpperTheory.mem_lattice_of_values_at_double_coset_reps :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (τ : X.Ub →* GL (Fin m) O) (φ : X.I.T →* Oˣ) (U : Subgroup X.Ub) (c : ℕ), W.c0 ≤ c → ∀ (N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) → ∀ F ∈ X.ClO W τ U c φ, ∀ Λ : Submodule O Ω, (∀ n i k, X.unt m W F i (x n) k ∈ Λ) → F ∈ X.Lat m W Λ := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m τ φ U c hc N x hx F hF Λ hΛ
  simp only [Frame.ClO, Frame.Cl, Submodule.mem_inf] at hF
  obtain ⟨⟨hA, hU⟩, hE⟩ := hF
  obtain ⟨hN, hNm, hT⟩ := hE
  have hA' : ∀ i γ g, F i (X.glob γ * g) =
      ((W.ξ (X.glob γ).2 : GL _ Ω) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ F i g :=
    fun i γ g => (Submodule.mem_pi.mp hA i (Set.mem_univ i)) γ g
  have hU' : ∀ u ∈ U, ∀ i g k,
      (((((GeneralLinearGroup.map (algebraMap O Ω)).comp τ) u : GL _ Ω) : Matrix (Fin m) (Fin m) Ω) *ᵥ
        (fun j => F j (g * ((u : Ga), 1)) k)) i = F i g k :=
    fun u hu i g k => congrFun (congrFun (congrFun (hU u hu) i) g) k
  have key : ∀ (h : Ga × Gp) (b : Gp) (s : O),
      (∀ i j, ((W.ξ b⁻¹ : GL _ Ω) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) i j ∈
        (algebraMap O Ω).range) →
      (∀ i, F i (h * (1, b)) = algebraMap O Ω s • F i h) →
      (∀ i k, X.unt m W F i h k ∈ Λ) → ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ := by
    intro h b s hMb hFb hG i k
    have e : X.unt m W F i (h * (1, b)) =
        ((W.ξ b⁻¹ : GL _ Ω) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ
          (algebraMap O Ω s • X.unt m W F i h) := by
      simp only [Frame.unt_apply, hFb i, Prod.snd_mul, map_mul, map_inv, _root_.mul_inv_rev,
        GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul]
    rw [e]
    refine detd_mulVec Λ _ hMb _ (fun j => ?_) k
    rw [Pi.smul_apply, smul_eq_mul, ← Algebra.smul_def]
    exact Λ.smul_mem s (hG i j)
  have stepN : ∀ h, ∀ b ∈ X.I.N, (∀ i k, X.unt m W F i h k ∈ Λ) →
      ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ := by
    intro h b hb hG
    refine key h b 1 (W.int_N _ (X.I.N.inv_mem hb)) (fun i => ?_) hG
    rw [map_one, one_smul]
    exact congrFun (congrFun (hN b hb) i) h
  have stepM : ∀ h, ∀ b ∈ X.I.Nm c, (∀ i k, X.unt m W F i h k ∈ Λ) →
      ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ := by
    intro h b hb hG
    refine key h b 1 (W.int_Nm _ (X.I.Nm_anti hc ((X.I.Nm c).inv_mem hb))) (fun i => ?_) hG
    rw [map_one, one_smul]
    exact congrFun (congrFun (hNm b hb) i) h
  have stepT : ∀ h, ∀ b ∈ X.I.T, (∀ i k, X.unt m W F i h k ∈ Λ) →
      ∀ i k, X.unt m W F i (h * (1, b)) k ∈ Λ := by
    intro h b hb hG
    refine key h b ((φ ⟨b, hb⟩)⁻¹ : Oˣ) (W.integral_torusCharacter _ (X.I.T.inv_mem hb)) (fun i => ?_) hG
    have := congrFun (congrFun (hT ⟨b, hb⟩) i) h
    refine this.trans ?_
    simp
  have stepU : ∀ h, ∀ u ∈ U, (∀ i k, X.unt m W F i h k ∈ Λ) →
      ∀ i k, X.unt m W F i (h * ((u : Ga), 1)) k ∈ Λ := by
    intro h u hu hG i k
    have hv : ∀ i, F i (h * ((u : Ga), 1)) =
        fun l => ∑ j, algebraMap O Ω (((τ u⁻¹ : GL _ O) : Matrix (Fin m) (Fin m) O) i j) * F j h l := by
      intro i
      funext l
      have := hU' u⁻¹ (U.inv_mem hu) i (h * ((u : Ga), 1)) l
      rw [← this]
      have hh : h * ((u : Ga), 1) * (((u⁻¹ : X.Ub) : Ga), (1 : Gp)) = h := by
        ext <;> simp
      simp only [Matrix.mulVec, dotProduct, hh]
      rfl
    have e : X.unt m W F i (h * ((u : Ga), 1)) k =
        ((Matrix.of fun a b => algebraMap O Ω (((τ u⁻¹ : GL _ O) : Matrix (Fin m) (Fin m) O) a b)) *ᵥ
          fun j => X.unt m W F j h k) i := by
      simp only [Frame.unt_apply, Prod.snd_mul, mul_one, hv, Matrix.mulVec, dotProduct, Finset.mul_sum,
        Matrix.of_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]
    exact detd_mulVec Λ _ (fun a b => ⟨_, rfl⟩) _ (fun j => hG j k) i
  have stepG : ∀ γ h, (∀ i k, X.unt m W F i h k ∈ Λ) →
      ∀ i k, X.unt m W F i (X.glob γ * h) k ∈ Λ := by
    intro γ h hG i k
    have e : X.unt m W F i (X.glob γ * h) = X.unt m W F i h := by
      rw [Frame.unt_apply, Frame.unt_apply, hA' i γ h]
      simp [Prod.snd_mul, Matrix.mulVec_mulVec, _root_.mul_inv_rev, mul_assoc]
    rw [e]
    exact hG i k
  show ∀ i g k, X.unt m W F i g k ∈ Λ
  intro i g k
  obtain ⟨γ, n, u, hu, b, hb, rfl⟩ := hx g
  obtain ⟨y1, hy1, t, ht, y2, hy2, rfl⟩ := ((iwMem Gp X.I c b).1).1 hb
  have eq : X.glob γ * x n * ((u : Ga), y1 * t * y2) =
      X.glob γ * (x n * ((u : Ga), 1) * (1, y1) * (1, t) * (1, y2)) := by
    ext <;> simp [mul_assoc]
  rw [eq]
  exact stepG γ _ (stepM _ y2 hy2 (stepT _ t ht (stepN _ y1 hy1
    (stepU _ u hu (fun i k => hΛ n i k))))) i k
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberPushforward
section
open MulAction

theorem UpperTheory.orbitalFiber_pushforward :
    UpperTheory.V.Z.Sym.Glob.Fib.Push := by
  intro H X' X _ _ _ H₀ q k hN hq hH₀ hk hT hfin hidx
  classical
  let F : orbitRel.Quotient H X → Set X' := fun i => {y | q y = Quotient.out i}
  letI act : ∀ i : orbitRel.Quotient H X, MulAction (stabilizer H (Quotient.out i)) (F i) := fun i =>
    { smul := fun h y => ⟨(h : H) • (y : X'), by
          show q ((h : H) • (y : X')) = Quotient.out i
          rw [hq, show q (y : X') = Quotient.out i from y.2]
          exact mem_stabilizer_iff.mp h.2⟩
      one_smul := fun y => Subtype.ext (one_smul H (y : X'))
      mul_smul := fun a b y => Subtype.ext (mul_smul (a : H) (b : H) (y : X')) }
  have hD := UpperTheory.orbitalFiber_decomposition H X' (orbitRel.Quotient H X) H₀ k
    (fun i => stabilizer H (Quotient.out i)) (fun i => F i)
    (fun i => (stabilizer H (Quotient.out i)).subtype) (fun i y => (y : X'))
    (fun i y => k (y : X')) hN hk hT
    (fun i h y => rfl) (fun i => Subtype.val_injective)
    (fun i h y => hk (h : H) (y : X')) (fun i y _ => rfl) ?cover ?disj
  case cover =>
    intro x hx
    obtain ⟨g, hg⟩ := orbitRel_apply.mp (Quotient.mk_out (s := orbitRel H X) (q x))
    refine ⟨Quotient.mk _ (q x), ⟨g • x, ?_⟩, g⁻¹, ?_, ?_⟩
    · show q (g • x) = _
      rw [hq]; exact hg
    · show k (g • x) ≠ 0
      rw [hk]; exact hx
    · show x = g⁻¹ • g • x
      rw [inv_smul_smul]
  case disj =>
    intro i j y y' h _ _ he
    have hqe : h • Quotient.out i = Quotient.out j := by
      have h1 : q (h • (y : X')) = q (y' : X') := congrArg q he
      rw [hq, show q (y : X') = Quotient.out i from y.2,
        show q (y' : X') = Quotient.out j from y'.2] at h1
      exact h1
    have hij : i = j := by
      rw [← Quotient.out_eq i, ← Quotient.out_eq j]
      exact (Quotient.sound (orbitRel_apply.mpr ⟨h, hqe⟩)).symm
    subst hij
    refine ⟨rfl, ?_⟩
    rw [Subgroup.range_subtype]
    exact mem_stabilizer_iff.mpr hqe
  rw [hD]
  conv_rhs => unfold UpperTheory.V.Z.Sym.gq
  refine finsum_congr (fun i => ?_)
  beta_reduce
  by_cases hz : ∃ y : X', q y = Quotient.out i ∧ k y ≠ 0
  · obtain ⟨y₀, hy₀, hk₀⟩ := hz
    have hind : (Subgroup.comap (stabilizer H (Quotient.out i)).subtype H₀).index ≠ 0 := by
      have := hidx y₀ hk₀
      rw [hy₀] at this
      exact this
    rw [UpperTheory.orbitalFiber_pushforward_eq_zero _ (F i) _ _ hind
      (fun z hz y => Subtype.ext (hH₀ (z : H) (Subgroup.mem_comap.mp hz) (y : X')))
      (fun h y => hk (h : H) (y : X'))
      (((hfin (Quotient.out i)).preimage Subtype.val_injective.injOn).subset
        (fun y hy => ⟨y.2, hy⟩))]
    rw [finsum_set_coe_eq_finsum_mem (f := k) (F i)]
    rfl
  · push_neg at hz
    have h0 : (∑ᶠ (y : X') (_ : q y = Quotient.out i), k y) = 0 := by
      apply finsum_eq_zero_of_forall_eq_zero
      intro y
      rw [finsum_eq_if]
      split_ifs with hy
      · exact hz y hy
      · rfl
    rw [h0, zero_div]
    unfold UpperTheory.V.Z.Sym.gq
    apply finsum_eq_zero_of_forall_eq_zero
    intro o
    beta_reduce
    rw [hz _ (Quotient.out o).2, zero_div]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberSingle
section
open MulAction in
theorem UpperTheory.orbitalFiber_single :
    UpperTheory.V.Z.Sym.Glob.Fib.OneFib := by
  intro Γ G _ _ ι S U' Γ₁ Γ₀ x Φ hcomm hΓS hN htriv hΦl hΦr hTex hst hrel hcard
  classical
  haveI hSn : S.Normal := ⟨fun n hn g => by
    convert S.mul_mem (hcomm g n) hn using 1
    group⟩
  set C := Subgroup.comap ι (S ⊔ U') with hC
  set f := (orbit ↥S (x : G ⧸ U')).indicator fun y => Φ (Quotient.out y) with hf
  have hΓC : Γ₁ ≤ C := fun a ha =>
    Subgroup.mem_comap.mpr ((le_sup_left : S ≤ S ⊔ U') (Subgroup.mem_comap.mp (hΓS ha)))
  let j : C →* G := ι.comp C.subtype
  let φ : Γ₁ →* C := Subgroup.inclusion hΓC
  have hclos : ∀ g ∈ S ⊔ U', ∀ y ∈ orbit ↥S (x : G ⧸ U'), g • y ∈ orbit ↥S (x : G ⧸ U') := by
    intro g hg y hy
    obtain ⟨s, hs, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    obtain ⟨⟨s', hs'⟩, rfl⟩ := hy
    refine ⟨⟨s * (u * (s' * x) * u⁻¹ * (s' * x)⁻¹) * s', S.mul_mem (S.mul_mem hs (hcomm _ _)) hs'⟩, ?_⟩
    show ((s * (u * (s' * x) * u⁻¹ * (s' * x)⁻¹) * s' * x : G) : G ⧸ U') = ((s * u * (s' * x) : G) : G ⧸ U')
    rw [QuotientGroup.eq]
    have he : (s * (u * (s' * x) * u⁻¹ * (s' * x)⁻¹) * s' * x)⁻¹ * (s * u * (s' * x)) = u := by group
    rw [he]
    exact hu
  have hinv : ∀ (h : C) (y : G ⧸ U'), f (j h • y) = f y := by
    intro h y
    have hg : ι h.1 ∈ S ⊔ U' := h.2
    change f (ι h.1 • y) = f y
    by_cases hy : y ∈ orbit ↥S (x : G ⧸ U')
    · have hy' := hclos _ hg y hy
      rw [hf, Set.indicator_of_mem hy', Set.indicator_of_mem hy]
      obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U' (ι h.1 * Quotient.out y)
      have hyy : ι h.1 • y = ((ι h.1 * Quotient.out y : G) : G ⧸ U') := by
        conv_lhs => rw [← QuotientGroup.out_eq' y]
        rfl
      rw [hyy, hu, hΦr _ u.2, hΦl]
    · have hy' : ι h.1 • y ∉ orbit ↥S (x : G ⧸ U') := fun hm => hy (by
        have := hclos _ (inv_mem hg) _ hm
        rwa [inv_smul_smul] at this)
      rw [hf, Set.indicator_apply, if_neg hy', Set.indicator_apply, if_neg hy]
  have hfin : ∃ T' : Finset (G ⧸ U'), ∀ y, f y ≠ 0 → ∃ h : C, ∃ x' ∈ T', y = j h • x' := by
    obtain ⟨T, hT⟩ := hTex
    refine ⟨T.image (QuotientGroup.mk : G → G ⧸ U'), ?_⟩
    intro y hy
    obtain ⟨⟨s, hs⟩, rfl⟩ := Set.mem_of_indicator_ne_zero hy
    obtain ⟨h, hh, t, ht, u, hu, he⟩ := hT s hs
    refine ⟨⟨h, hΓC hh⟩, (t : G ⧸ U'), Finset.mem_image_of_mem QuotientGroup.mk ht, ?_⟩
    show ((s * x : G) : G ⧸ U') = ((ι h * t : G) : G ⧸ U')
    rw [he, QuotientGroup.eq]
    rw [show (ι h * t * u)⁻¹ * (ι h * t) = u⁻¹ by group]
    exact inv_mem hu
  have hsup : φ.range ⊔ Γ₀.subgroupOf C = (Γ₁ ⊔ Γ₀).subgroupOf C := by
    ext z
    rw [Subgroup.mem_sup_of_normal_right, Subgroup.mem_subgroupOf, Subgroup.mem_sup_of_normal_right]
    constructor
    · rintro ⟨a, ⟨a', rfl⟩, b, hb, rfl⟩
      exact ⟨a'.1, a'.2, b.1, Subgroup.mem_subgroupOf.mp hb, rfl⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      have hbC : b ∈ C := by
        have hb' : b = a⁻¹ * (z : Γ) := by rw [← hab]; group
        rw [hb']
        exact C.mul_mem (C.inv_mem (hΓC ha)) z.2
      exact ⟨φ ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, ⟨b, hbC⟩, Subgroup.mem_subgroupOf.mpr hb, Subtype.ext hab⟩
  have hidx : (φ.range ⊔ Γ₀.subgroupOf C).index = (Γ₁ ⊔ Γ₀).relIndex C := by
    rw [hsup]
    rfl
  have key := UpperTheory.V.Z.Sym.Tf.gqIndex Γ₁ C G φ j (Γ₀.subgroupOf C) U' f
    inferInstance (fun z hz y => htriv z.1 (Subgroup.mem_subgroupOf.mp hz) y)
    (by rw [hidx]; exact hrel) hinv hfin
    (fun y _ => by
      rw [← Subgroup.comap_comap]
      exact Subgroup.relIndex_comap_ne_zero _ (hst y))
  have e1 : UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) (Γ₀.subgroupOf Γ₁) U' f =
      UpperTheory.V.Z.Sym.gqOn (j.comp φ) (Subgroup.comap φ (Γ₀.subgroupOf C)) U' f := rfl
  have hb : UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) (Γ₀.subgroupOf Γ₁) U' f =
      ↑(Nat.card ↥(Γ₀.subgroupOf Γ₁)) * UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) ⊥ U' f := by
    letI := MulAction.compHom (G ⧸ U') (ι.comp Γ₁.subtype)
    exact (UpperTheory.orbitalFiber_of_bot Γ₁ (G ⧸ U') (Γ₀.subgroupOf Γ₁) f).2 hcard
      (fun z hz y => htriv z.1 (Subgroup.mem_subgroupOf.mp hz) y)
  rw [← hb, e1, key, hidx]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SigLEqOfHermSemilinearEqStar
section
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

section SlopeTestRemainingChoices

variable {K : Type} [Field K] {Δ τ : K}

private theorem sigL_mul' (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by
  ext <;> simp [sigL]

private theorem sigL_sigL' (x : EL Δ τ) : sigL (sigL x) = x := by
  ext <;> simp [sigL]

private theorem sigL_one' : sigL (1 : EL Δ τ) = 1 := by
  ext <;> simp [sigL, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem trace_sigL (x : EL Δ τ) : QuadraticAlgebra.trace (sigL x) = star (QuadraticAlgebra.trace x) := by
  have e : star (algebraMap K (Lsq K Δ) τ) = algebraMap K (Lsq K Δ) τ := by
    ext <;> simp
  simp [QuadraticAlgebra.trace_def, sigL, e]

private theorem eq_zero_of_trace (hτ : τ ^ 2 - 4 ≠ 0) {w : EL Δ τ}
    (h : ∀ x, QuadraticAlgebra.trace (w * x) = 0) : w = 0 := by
  have h1 := h 1
  have h2 := h QuadraticAlgebra.omega
  simp [QuadraticAlgebra.trace_def] at h1 h2
  have hu : IsUnit (algebraMap K (Lsq K Δ) (τ ^ 2 - 4)) := (IsUnit.mk0 _ hτ).map _
  rw [map_sub, map_pow, map_ofNat] at hu
  refine QuadraticAlgebra.ext ?_ ?_
  · refine hu.mul_right_eq_zero.1 ?_
    linear_combination ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * h1 - (algebraMap K (Lsq K Δ) τ) * h2
  · refine hu.mul_right_eq_zero.1 ?_
    linear_combination 2 * h2 - (algebraMap K (Lsq K Δ) τ) * h1

end SlopeTestRemainingChoices

theorem UpperTheory.sigL_eq_of_herm_semilinear_eq_star :
    ∀ (K : Type) [Field K] [CharZero K] (Δ τ c : K) (d m : EL Δ τ), τ ^ 2 - 4 ≠ 0 →
        (∀ x y : Sp Δ τ, herm c m (semi d x) (semi d y) = star (herm c m x y)) → sigL m = m * d * star (sigL d) := by
  intro K _ _ Δ τ c d m hτ h
  have key : ∀ a : EL Δ τ, QuadraticAlgebra.trace ((m * d * star (sigL d) - sigL m) * a) = 0 := fun a => by
    have e := h (0, sigL a) (0, 1)
    simp only [herm, semi, star_zero, mul_zero, zero_mul, zero_add, sigL_sigL', sigL_one', mul_one, star_one,
      sigL_mul'] at e
    rw [← trace_sigL, sigL_mul', sigL_sigL'] at e
    rw [sub_mul, map_sub, sub_eq_zero, ← e]
    congr 1
    ring
  exact (sub_eq_zero.1 (eq_zero_of_trace hτ key)).symm
end

