module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Bundle0001
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.SymmetricFourthPowerMatrix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.ConjOn
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.conjOn :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (H : Type) [Group H] (n : ℕ) (R R' : H →* GL (Fin n) k), IsIrr R → ∀ x₀ y₀ : GL (Fin n) k, (∀ h, Ga.tr (x₀ * R h) = Ga.tr (y₀ * R' h)) → RepIso R R' := by
  intro k _ _ H _ n R R' hR x₀ y₀ htr
  classical
  let φ : H →* Matrix (Fin n) (Fin n) k := (Units.coeHom _).comp R'
  let ψ : H →* Matrix (Fin n) (Fin n) k := (Units.coeHom _).comp R
  let f : Matrix (Fin n) (Fin n) k →ₗ[k] k :=
    (Matrix.traceLinearMap (Fin n) k k) ∘ₗ LinearMap.mulLeft k (y₀ : Matrix (Fin n) (Fin n) k)
  obtain ⟨hdim, hker⟩ := Ga.kerLe k H n R hR x₀ (Matrix (Fin n) (Fin n) k) φ f
    (fun h => by simpa [f, φ, Ga.tr] using htr h)
  have htop : Algebra.adjoin k (Set.range φ) = ⊤ := by
    apply Subalgebra.toSubmodule_injective
    apply Submodule.eq_top_of_finrank_eq
    apply le_antisymm (Submodule.finrank_le _)
    simpa [Module.finrank_matrix, sq] using hdim
  let P : MonoidAlgebra k H →ₐ[k] Matrix (Fin n) (Fin n) k := MonoidAlgebra.lift k _ H φ
  let Q : MonoidAlgebra k H →ₐ[k] Matrix (Fin n) (Fin n) k := MonoidAlgebra.lift k _ H ψ
  have hs : Function.Surjective P := by
    have hle : Algebra.adjoin k (Set.range φ) ≤ P.range :=
      Algebra.adjoin_le (by
        rintro _ ⟨h, rfl⟩
        exact ⟨MonoidAlgebra.of k H h, by simp [P]⟩)
    intro m
    have hm : m ∈ P.range := hle (htop ▸ Algebra.mem_top)
    exact hm
  have hk : ∀ a ∈ RingHom.ker P, Q a = 0 := fun a ha => hker a ha
  let T : Matrix (Fin n) (Fin n) k →ₐ[k] Matrix (Fin n) (Fin n) k :=
    (Ideal.Quotient.liftₐ (RingHom.ker P) Q hk).comp
      (Ideal.quotientKerAlgEquivOfSurjective hs).symm.toAlgHom
  have hT : ∀ h, T (φ h) = ψ h := by
    intro h
    have h1 : (Ideal.quotientKerAlgEquivOfSurjective hs).symm (φ h) =
        Ideal.Quotient.mk (RingHom.ker P) (MonoidAlgebra.of k H h) := by
      rw [AlgEquiv.symm_apply_eq]
      simp [P]
    change Ideal.Quotient.liftₐ (RingHom.ker P) Q hk
      ((Ideal.quotientKerAlgEquivOfSurjective hs).symm (φ h)) = ψ h
    rw [h1]
    change Q (MonoidAlgebra.of k H h) = ψ h
    simp [Q]
  obtain ⟨J, hJ⟩ := KStar.Tree.exists_conj_of_algHom T
  refine ⟨J⁻¹, fun s => ?_⟩
  have h2 := hJ (φ s)
  rw [hT] at h2
  have h3 : R s * J = J * R' s := Units.ext h2
  rw [inv_inv, mul_assoc, h3, inv_mul_cancel_left]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.NoKappa
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private def phiB {k : Type} [Field k] {H : Type} [Group H] (a b : H →* GL (Fin 3) k) :
    H →* (Matrix (Fin 3) (Fin 3) k × Matrix (Fin 3) (Fin 3) k × k) where
  toFun h := ((a h : Matrix (Fin 3) (Fin 3) k), (b h : Matrix (Fin 3) (Fin 3) k), 1)
  map_one' := by simp
  map_mul' x y := by simp

private def fB {k : Type} [Field k] (A B : Matrix (Fin 3) (Fin 3) k) :
    (Matrix (Fin 3) (Fin 3) k × Matrix (Fin 3) (Fin 3) k × k) →ₗ[k] k :=
  (Matrix.traceLinearMap (Fin 3) k k ∘ₗ LinearMap.mulLeft k A ∘ₗ LinearMap.fst k _ _) +
    (Matrix.traceLinearMap (Fin 3) k k ∘ₗ LinearMap.mulLeft k B ∘ₗ LinearMap.fst k _ _ ∘ₗ LinearMap.snd k _ _) -
    (LinearMap.snd k _ _ ∘ₗ LinearMap.snd k _ _)

private theorem fB_apply {k : Type} [Field k] (A B X Y : Matrix (Fin 3) (Fin 3) k) (z : k) :
    fB A B (X, Y, z) = (A * X).trace + (B * Y).trace - z := by
  simp [fB]

theorem UpperTheory.V.Z.Sym.Ga.noKappa :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (r r' : Γ →* GL (Fin 2) (Qbar l)), IrrOpen (Ga.sym4 r) → ∀ V : Set Γ, IsOpen V → V.Nonempty → (∀ g ∈ V, Ga.uf (r' g) = Ga.uf (r g) ^ 2 - 2) → False := by
  intro l _ Γ _ _ _ _ _ r r' hirr V hV ⟨g, hg⟩ hu
  obtain ⟨H, -, hHo, hH⟩ := Ga.coset Γ V hV g hg
  have hR : IsIrr ((Ga.sym4 r).comp H.subtype) := hirr H hHo
  have key := Ga.kerLe (Qbar l) H 5 ((Ga.sym4 r).comp H.subtype) hR (Ga.sym4 r g)
    (Matrix (Fin 3) (Fin 3) (Qbar l) × Matrix (Fin 3) (Fin 3) (Qbar l) × Qbar l)
    (phiB ((ad0 r).comp H.subtype) ((ad0 r').comp H.subtype))
    (fB (ad0 r g : Matrix (Fin 3) (Fin 3) (Qbar l)) (ad0 r' g)) ?_
  · have h1 := key.1
    have h2 : Module.finrank (Qbar l) ↥(Algebra.adjoin (Qbar l)
        (Set.range ⇑(phiB ((ad0 r).comp H.subtype) ((ad0 r').comp H.subtype)))) ≤ 19 := by
      refine (Submodule.finrank_le (Subalgebra.toSubmodule (Algebra.adjoin (Qbar l)
        (Set.range ⇑(phiB ((ad0 r).comp H.subtype) ((ad0 r').comp H.subtype)))))).trans ?_
      simp [Module.finrank_prod, Module.finrank_matrix]
    omega
  · intro h
    have hgh := hu (g * h) (hH h h.2)
    have e1 : Ga.tr (Ga.sym4 r g * ((Ga.sym4 r).comp H.subtype) h) = Ga.tr (Ga.sym4 r (g * h)) := by
      simp [map_mul]
    have e2 : ((ad0 r g : Matrix (Fin 3) (Fin 3) (Qbar l)) * (ad0 r (h : Γ))).trace
        = Ga.uf (r (g * h)) + 1 := by
      rw [← (Ga.ufFacts (Qbar l) (r (g * h))).2.2.2.2 Γ r (g * h), map_mul]
      rfl
    have e3 : ((ad0 r' g : Matrix (Fin 3) (Fin 3) (Qbar l)) * (ad0 r' (h : Γ))).trace
        = Ga.uf (r' (g * h)) + 1 := by
      rw [← (Ga.ufFacts (Qbar l) (r' (g * h))).2.2.2.2 Γ r' (g * h), map_mul]
      rfl
    rw [e1, Ga.trSym4]
    show _ = fB _ _ ((((ad0 r).comp H.subtype) h : Matrix (Fin 3) (Fin 3) (Qbar l)),
      (((ad0 r').comp H.subtype) h : Matrix (Fin 3) (Fin 3) (Qbar l)), 1)
    rw [fB_apply]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [e2, e3, hgh]
    ring
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.RegElt
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem regElt_place {Ω : Type} [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  have hI : Ideal.span {((p : ℕ) : (Int.castRingHom Ω).range)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top, isUnit_iff_exists_inv]
    rintro ⟨⟨_, c, rfl⟩, hc⟩
    have h1 : ((p : ℕ) : Ω) * ((c : ℤ) : Ω) = 1 := congrArg Subtype.val hc
    have h2 : ((p : ℕ) : ℤ) * c = 1 := by exact_mod_cast h1
    have h3 : ((p : ℕ) : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) h2
    exact hp.one_lt.ne' (by exact_mod_cast h3)
  obtain ⟨A, -, hA⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨A, A.mem_nonunits_iff.1 (hA ⟨((p : ℕ) : (Int.castRingHom Ω).range), Ideal.mem_span_singleton_self _, by simp⟩)⟩

private theorem regElt_zpow_ne {G : Type} [Group G] (e : G) (he : ¬ IsOfFinOrder e) (n : ℤ) (hn : 0 < n) : e ^ n ≠ 1 := by
  intro h
  refine he (isOfFinOrder_iff_pow_eq_one.2 ⟨n.toNat, by omega, ?_⟩)
  rw [← zpow_natCast, Int.toNat_of_nonneg hn.le, h]

private theorem regElt_key {K : Type} [Field K] (e x : Kˣ) (m k : ℕ) (hm : 2 ≤ m) (hk : 0 < k)
    (hx : x ^ k = (e ^ (m : ℤ)) ^ k) (he : ¬ IsOfFinOrder e) :
    ¬ IsOfFinOrder x ∧ ∀ i : ℤ, |i| ≤ 2 →
      ((x : K) + ((x⁻¹ : Kˣ) : K)) ^ 2 - 2 ≠ (e : K) ^ i + (e : K) ^ (-i) := by
  have hsq : ∀ j : ℤ, |j| ≤ 2 → x ^ 2 ≠ e ^ j := by
    intro j hj h
    have hj' := (abs_le.1 hj).2
    have hpos : 0 < (2 * (m : ℤ) - j) * (k : ℤ) := by
      have : (0 : ℤ) < k := by exact_mod_cast hk
      have : (2 : ℤ) ≤ m := by exact_mod_cast hm
      apply mul_pos <;> omega
    refine regElt_zpow_ne e he _ hpos ?_
    have h1 : (e ^ (m : ℤ)) ^ k * (e ^ (m : ℤ)) ^ k = (e ^ j) ^ k := by
      rw [← hx, ← h, ← pow_add, ← pow_mul, two_mul]
    have h2 : e ^ ((2 * (m : ℤ) - j) * (k : ℤ)) = (e ^ (m : ℤ)) ^ k * (e ^ (m : ℤ)) ^ k * ((e ^ j) ^ k)⁻¹ := by
      simp only [← zpow_natCast, ← zpow_mul, ← zpow_neg, ← zpow_add]
      congr 1
      ring
    rw [h2, h1, mul_inv_cancel]
  refine ⟨fun hf => ?_, fun i hi h => ?_⟩
  · obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
    have hpos : 0 < (m : ℤ) * k * n := by
      have a : (0 : ℤ) < m := by exact_mod_cast (by omega : 0 < m)
      have b : (0 : ℤ) < k := by exact_mod_cast hk
      have c : (0 : ℤ) < n := by exact_mod_cast hn
      positivity
    refine regElt_zpow_ne e he _ hpos ?_
    rw [zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ← hx, ← pow_mul, mul_comm, pow_mul, h, one_pow]
  · have hx0 : (x : K) ≠ 0 := x.ne_zero
    have hE0 : ((e : K) ^ i) ≠ 0 := zpow_ne_zero _ e.ne_zero
    have hz : ((x : K) ^ 2 - (e : K) ^ i) * ((x : K) ^ 2 - ((e : K) ^ i)⁻¹) = 0 := by
      rw [Units.val_inv_eq_inv_val, zpow_neg] at h
      field_simp at h ⊢
      linear_combination (exp := 1) h
    rcases mul_eq_zero.1 hz with h0 | h0
    · refine hsq i hi (Units.ext ?_)
      rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val]
      exact sub_eq_zero.1 h0
    · refine hsq (-i) (by rwa [abs_neg]) (Units.ext ?_)
      rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, zpow_neg]
      exact sub_eq_zero.1 h0

theorem UpperTheory.V.Z.Sym.Ga.regElt :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (M m : ℕ) (r : G L Ω →* GL (Fin 2) (Qbar l)), AdIn ι M m r → ∀ H : Subgroup (G L Ω), IsOpen (H : Set (G L Ω)) → ∃ s ∈ H, s ∉ Ga.Bad r ∧ ∃ a b : (Qbar l)ˣ, ¬ IsOfFinOrder (a / b) ∧ (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C (a : Qbar l)) * (X - C (b : Qbar l)) := by
  intro L Ω _ _ _ _ _ _ l _ ι M m r hr H hH
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  obtain ⟨A, hA⟩ := regElt_place (Ω := Ω) l (Fact.out)
  obtain ⟨b0, k, κ, hk, ⟨g, hg⟩, hκ⟩ := hr.above A hA
  obtain ⟨s, hsH, hsI, hinf⟩ := UpperTheory.V.Z.Sym.Ga.ineInf L Ω l A hA H hH
  let t : ↥(Dec (F := L) A) := ⟨s, Ine_le_Dec A hsI⟩
  obtain ⟨h0, h1⟩ := hκ t hsI
  have hcp : (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C ((κ 0 t : (Qbar l)ˣ) : Qbar l)) * (X - C ((κ 1 t : (Qbar l)ˣ) : Qbar l)) := by
    have e : ((g * r s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly =
        (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
      exact Matrix.charpoly_units_conj g _
    rw [← e, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => (hg t).1 i j hij), Fin.prod_univ_two]
    have e0 : ((g * r s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((κ 0 t : (Qbar l)ˣ) : Qbar l) := (hg t).2 0
    have e1 : ((g * r s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = ((κ 1 t : (Qbar l)ˣ) : Qbar l) := (hg t).2 1
    rw [e0, e1]
  have hx : (κ 0 t / κ 1 t) ^ k = (cycBar L Ω l s ^ (m : ℤ)) ^ k := by
    rw [div_pow, h0, h1, zpow_add, mul_pow]
    exact mul_div_cancel_left _ _
  have key := regElt_key (cycBar L Ω l s) (κ 0 t / κ 1 t) m k hr.gap hk hx hinf
  refine ⟨s, hsH, ?_, κ 0 t, κ 1 t, key.1, hcp⟩
  rintro ⟨i, hi, hb⟩
  have huf := (UpperTheory.V.Z.Sym.Ga.ufFacts _ (r s)).1 _ _ hcp
  rw [huf] at hb
  exact key.2 i hi hb
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Spread
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.spread :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω], Unr L → ∀ E B : Set (G L Ω), IsClosed E → IsClosed B → (∀ c : G (maximalRealSubfield L) Ω, IsConjEl c → ∀ s s' : G L Ω, s'.restrictScalars (maximalRealSubfield L) = c * s.restrictScalars (maximalRealSubfield L) * c⁻¹ → s' ∈ E → s ∈ E) → ∀ (P : Set (Plc L)) (M : ℕ), M ≠ 0 → (∀ w, IsSplitAt w → (M : 𝓞 L) ∉ w.asIdeal → (∃ s, Ga.FrobAt w s ∧ s ∉ B) → ∃ w' ∈ P, w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) → (∀ᶠ w in Filter.cofinite, w ∈ P → ∀ s, Ga.FrobAt w s → s ∈ E) → Bᶜ ⊆ E := by
  intro L Ω _ _ _ _ _ _ hU E B hE hB hconj P M hM hsplit hev
  classical
  obtain ⟨c, hc⟩ := Ga.conjEx L Ω
  have hbad : {w : Plc L | ¬ (w ∈ P → ∀ s, Ga.FrobAt w s → s ∈ E)}.Finite :=
    Filter.eventually_cofinite.mp hev
  let T : Set (HeightOneSpectrum (𝓞 L)) :=
    ⋃ w ∈ {w : Plc L | ¬ (w ∈ P → ∀ s, Ga.FrobAt w s → s ∈ E)},
      {v | HeightOneSpectrum.under (𝓞 (Lp L)) w = HeightOneSpectrum.under (𝓞 (Lp L)) v}
  have hT : T.Finite := by
    refine hbad.biUnion fun w _ => ?_
    have hfin := IsDedekindDomain.primesOver_finite
      (HeightOneSpectrum.under (𝓞 (Lp L)) w).asIdeal (𝓞 L)
    refine (hfin.preimage (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    intro v hv
    refine ⟨v.isPrime, ⟨?_⟩⟩
    rw [hv]
    rfl
  have hMne : ((M : 𝓞 L) : 𝓞 L) ≠ 0 := by exact_mod_cast hM
  have hMfin : {v : HeightOneSpectrum (𝓞 L) | (M : 𝓞 L) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(M : 𝓞 L)}) ?_).subset ?_
    · rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hMne
    · intro v hv
      exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hv)
  have hS : ({v : HeightOneSpectrum (𝓞 L) | (M : 𝓞 L) ∈ v.asIdeal} ∪ T).Finite := hMfin.union hT
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := L) (Ω := Ω)
    GlobalTheory.Published.chebotarevDegreeOne' hS
  intro σ hσB
  have hcl := hD.open_subset_closure_inter hB.isOpen_compl hσB
  refine closure_minimal ?_ hE hcl
  rintro τ ⟨hτB, v, hvS, hdeg, A, hA, hfr⟩
  have hFrob : Ga.FrobAt v τ := ⟨A, hA, hfr⟩
  have hMv : (M : 𝓞 L) ∉ v.asIdeal := fun h => hvS (Or.inl h)
  have hspl : IsSplitAt v := UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one L v (hU v) hdeg
  obtain ⟨w', hw'P, hw'⟩ := hsplit v hspl hMv ⟨τ, hFrob, hτB⟩
  have hgood : ∀ s, Ga.FrobAt w' s → s ∈ E := by
    by_contra hcon
    exact hvS (Or.inr (Set.mem_biUnion (x := w') (fun h => hcon (h hw'P)) hw'))
  rcases Ga.conjFrob L Ω c hc v w' hw' τ hFrob with h1 | ⟨s', hs', hres⟩
  · exact hgood τ h1
  · exact hconj c hc τ s' hres (hgood s' hs')
end
end

