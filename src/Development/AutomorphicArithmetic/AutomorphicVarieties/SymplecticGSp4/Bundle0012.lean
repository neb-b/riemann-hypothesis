module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0043

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocVanP
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem lv_gen (hP : Loc.LocalPublishedTheorems) {v l : ℕ} [Fact v.Prime] [Fact l.Prime] (hvl : v ≠ l) {H : Type} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →* Formalism.BasicNotions.Loc.GQ v) (hφ : Topology.IsOpenEmbedding φ)
    (k : Type) [Field k] [Finite k] [CharP k l] [Algebra ℤ_[l] k] (κ : H →* kˣ) (hκ : IsOpen (κ.ker : Set H))
    (σ : H) (h1 : κ σ ≠ 1) (h2 : Loc.cycA v l k (φ σ) = 1) (z : H → k) (hz : IsLocallyConstant z)
    (hc : ∀ g h, z (g * h) = z g + (κ g : k) * z h) : ∃ m, ∀ g, z g = (κ g : k) * m - m := by
  letI : TopologicalSpace k := ⊥
  haveI : DiscreteTopology k := ⟨rfl⟩
  have h1' : (κ σ : k) ≠ 1 := fun h => h1 (Units.ext h)
  have hρ : ∀ g x, Loc.chRep κ g x = (κ g : k) * x := fun _ _ => rfl
  have hlc : IsLocallyConstant κ := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(fun h => g⁻¹ * h) ⁻¹' (κ.ker : Set H),
      hκ.preimage (continuous_const.mul continuous_id), by simp, fun h hh => ?_⟩
    have : κ (g⁻¹ * h) = 1 := hh
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this.symm
  have hca : ContAction (Loc.chRep κ) := by
    unfold ReciprocityTheory.Gal.ContAction
    rw [continuous_prod_of_discrete_right]
    intro y
    exact (hlc.comp fun u : kˣ => (u : k) * y).continuous
  obtain ⟨f1, f2, e1, e2⟩ := Loc.tateFin hP φ hφ k k (Loc.chRep κ) hca
  have z0 : H0 (Loc.chRep κ) = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    have := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm σ
    rw [hρ] at this
    rw [Submodule.mem_bot]
    by_contra h
    exact h1' (mul_right_cancel₀ h (by rw [this, one_mul]))
  have z2 : Loc.H0dual ((Loc.cycA v l k).comp φ) (Loc.chRep κ) = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Submodule.mem_bot]
    refine LinearMap.ext fun x => ?_
    have := hf σ x
    rw [MonoidHom.comp_apply, h2, hρ, ← smul_eq_mul, map_smul, smul_eq_mul, Units.val_one] at this
    by_contra h
    exact h1' (mul_right_cancel₀ h this)
  rw [e2, z0, z2, if_neg hvl, finrank_bot, finrank_bot] at e1
  haveI : Subsingleton (H1 (Loc.chRep κ)) := Module.finrank_zero_iff.1 e1
  have hz1 : z ∈ Z1 (Loc.chRep κ) := ⟨hz.continuous, hc⟩
  have : (Submodule.Quotient.mk ⟨z, hz1⟩ : H1 (Loc.chRep κ)) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1] at this
  exact this

private theorem lv_dec (hP : Loc.LocalPublishedTheorems) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {v l : ℕ} (hv : v.Prime)
    [Fact l.Prime] (hvl : v ≠ l) (A : ValuationSubring Ω) (hA : A.valuation (v : Ω) < 1)
    (k : Type) [Field k] [Finite k] [CharP k l] [Algebra ℤ_[l] k] (κ : Dec (F := ℚ) A →* kˣ)
    (hκ : IsOpen (κ.ker : Set (Dec (F := ℚ) A))) (σ : Dec (F := ℚ) A) (h1 : κ σ ≠ 1)
    (h2 : algebraMap ℤ_[l] k (cycZ ℚ Ω l σ : ℤ_[l]ˣ) = 1) (z : Dec (F := ℚ) A → k) (hz : IsLocallyConstant z)
    (hc : ∀ g h, z (g * h) = z g + (κ g : k) * z h) : ∃ m, ∀ g, z g = (κ g : k) * m - m := by
  haveI : Fact v.Prime := ⟨hv⟩
  obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := v) (F := ℚ) A hA
  obtain ⟨j, rfl⟩ := (Loc.decEmb (F := ℚ) (Ω := Ω) (v := v)).1 A w hAw hw
  obtain ⟨φ, hφ, -, -, -, hcyc, -⟩ := ((Loc.decEmb (F := ℚ) (Ω := Ω) (v := v)).2 j).2
  refine lv_gen hP hvl φ hφ k κ hκ σ h1 (Units.ext ?_) z hz hc
  rw [← hcyc l σ] at h2
  exact h2

private theorem lv_red {O k : Type} [CommRing O] [IsLocalRing O] [Field k] (red : O →+* k)
    (hred : ∀ a ∈ maximalIdeal O, red a = 0) (a b : O) : red a = red b ↔ residue O a = residue O b := by
  rw [← sub_eq_zero, ← map_sub, ← sub_eq_zero (a := residue O a), ← map_sub, residue_eq_zero_iff]
  refine ⟨fun h => ?_, hred _⟩
  by_contra hn
  exact ((IsLocalRing.notMem_maximalIdeal.1 hn).map red).ne_zero h

theorem UpperTheory.V.GradeZeroInterpolatingElement.locVanP :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → Loc.LocalPublishedTheorems → ∀ (k : Type) [Field k] [Finite k] (red : c.O →+* k), (∀ a ∈ maximalIdeal c.O, red a = 0) → ∀ γ ∈ [D.al, D.be, D.th, D.al⁻¹, D.be⁻¹, D.th⁻¹], ∀ p ∈ D.Sb, ∀ z : D.Gp p → k, IsLocallyConstant z → (∀ g h : D.Gp p, z (g * h) = z g + red (γ g : c.O) * z h) → ∃ m, ∀ g : D.Gp p, z g = red (γ g : c.O) * m - m := by
  intro Ω _ _ _ l _ c D hD hP k _ _ red hred γ hγ p hp z hz hc
  obtain ⟨f1, f2, -, -, -, -, -, -, -, -, -, fo, -⟩ := facts D hD
  obtain ⟨hpp, hpl, -, -⟩ := f1 p hp
  obtain ⟨hσ, hom, hne⟩ := f2 p (Finset.mem_insert_of_mem hp)
  have hl : l.Prime := Fact.out
  obtain ⟨i, j, hij, hγ'⟩ : ∃ i j, lamW i ≠ lamW j ∧ ∀ g, γ g * D.ps j g = D.ps i g := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨2, 3, by decide, fun g => by simp [Raw.ps]⟩
    · exact ⟨1, 2, by decide, fun g => by simp [Raw.ps, Raw.be]⟩
    · exact ⟨0, 3, by decide, fun g => by simp [Raw.ps]⟩
    · exact ⟨3, 2, by decide, fun g => by simp [Raw.ps]⟩
    · exact ⟨2, 1, by decide, fun g => by simp [Raw.ps, Raw.be]⟩
    · exact ⟨3, 0, by decide, fun g => by simp [Raw.ps]⟩
  have hγr : ∀ g, red (γ g : c.O) * red (D.ps j g : c.O) = red (D.ps i g : c.O) := fun g => by
    rw [← map_mul, ← Units.val_mul, hγ']
  letI : Algebra ℤ_[l] k := (red.comp (algebraMap ℤ_[l] c.O)).toAlgebra
  have hl0 : (l : k) = 0 := by
    have hloc := (dvrFacts l c.O).2.2.1
    have hm : (l : c.O) ∈ maximalIdeal c.O := by
      rw [mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O), isUnit_map_iff]
      exact PadicInt.p_nonunit
    simpa using hred _ hm
  haveI : CharP k l := (CharP.charP_iff_prime_eq_zero hl).2 hl0
  let κ : D.Gp p →* kˣ := ((Units.map red.toMonoidHom).comp γ).comp (D.Gp p).subtype
  have hκ : ∀ g : D.Gp p, (κ g : k) = red (γ g : c.O) := fun _ => rfl
  have hker : D.rbar.ker.comap (D.Gp p).subtype ≤ κ.ker := by
    intro g hg
    have hg' : D.rbar g = 1 := hg
    have h1 : ∀ a, red (D.ps a g : c.O) = 1 := fun a => by
      rw [← map_one red, lv_red red hred, map_one]
      have := congrFun (congrFun hg' a) a
      simpa [Raw.rbar, Raw.r0, diagRep] using this
    refine Units.ext ?_
    have := hγr g
    rw [h1, h1, mul_one] at this
    exact this
  refine lv_dec hP hpp hpl (D.pl p) (hD.pl_over p hpp) k κ
    (Subgroup.isOpen_mono hker (fo.preimage continuous_subtype_val)) ⟨D.sg p, hσ⟩ (fun h => ?_) ?_ z hz hc
  · have h' : red (γ (D.sg p) : c.O) = 1 := congrArg Units.val h
    have := hγr (D.sg p)
    rw [h', one_mul, lv_red red hred] at this
    exact hne i j hij this.symm
  · have : red (chiO ℚ Ω l c.O (D.sg p) : c.O) = red 1 := by
      rw [lv_red red hred, map_one]
      exact (hD.om_bar _).symm.trans hom
    rw [map_one] at this
    exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.NumsZero
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem nums_odd {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) {j : ℤ × ℤ} (hj : j ∈ oddRoots) :
    D.XVan (D.al ^ j.1 * D.Psi ^ j.2) ∧ (j.1 = 1 ∨ j.1 = -1) ∧
      ∃ a b, lamW a ≠ lamW b ∧ D.al ^ j.1 * D.Psi ^ j.2 * D.ps b = D.ps a := by
  have h1 := hD.xvan D.al (by simp)
  have h2 := hD.xvan D.be (by simp)
  have h3 := hD.xvan D.th (by simp)
  simp only [oddRoots, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · have e : D.al ^ wAl.1 * D.Psi ^ wAl.2 = D.al := by simp [wAl]
    rw [e]
    exact ⟨h1.1, by decide, 2, 3, by decide, by simp [Raw.ps]⟩
  · have e : D.al ^ (-wAl).1 * D.Psi ^ (-wAl).2 = D.al⁻¹ := by simp [wAl]
    rw [e]
    exact ⟨h1.2, by decide, 3, 2, by decide, by simp [Raw.ps]⟩
  · have e : D.al ^ wBe.1 * D.Psi ^ wBe.2 = D.be := by simp [wBe, Raw.be, mul_comm]
    rw [e]
    exact ⟨h2.1, by decide, 1, 2, by decide, by simp [Raw.ps, Raw.be]⟩
  · have e : D.al ^ (-wBe).1 * D.Psi ^ (-wBe).2 = D.be⁻¹ := by simp [wBe, Raw.be, mul_comm]
    rw [e]
    exact ⟨h2.2, by decide, 2, 1, by decide, by simp [Raw.ps, Raw.be]⟩
  · have e : D.al ^ wTh.1 * D.Psi ^ wTh.2 = D.th := by simp [wTh, Raw.th]
    rw [e]
    exact ⟨h3.1, by decide, 0, 3, by decide, by simp [Raw.ps]⟩
  · have e : D.al ^ (-wTh).1 * D.Psi ^ (-wTh).2 = D.th⁻¹ := by simp [wTh, Raw.th, mul_comm]
    rw [e]
    exact ⟨h3.2, by decide, 3, 0, by decide, by simp [Raw.ps]⟩

private theorem nums_lc {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker ψ h

private theorem nums_gen (P : CohomologyHyp) {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}
    (hG : X.GalData l SP T Q pl K) (hK : IsOpen (K : Set (G ℚ Ω))) {k : Type} [Field k] [Finite k] [CharP k l] {M : Type}
    [AddCommGroup M] [Module k M] [Module.Finite k M] (ρ : Representation k (GS Ω SP) M) (γ : G ℚ Ω →* kˣ)
    (hγ : ∀ g m, ρ (toGS Ω SP g) m = (γ g : k) • m) (hKγ : K ≤ γ.ker) {σ : G ℚ Ω} (hσ : IsCC σ)
    (hd : Module.finrank k M = 0 ∨ ∃ g, γ g ≠ X.cycK Ω l k g) :
    Module.Finite k ((X.galFrame SP T Q v0 pl K).Ob ρ) ∧
      (γ σ = 1 → Module.finrank k ((X.galFrame SP T Q v0 pl K).Ob ρ) =
        Module.finrank k ((X.galFrame SP T Q v0 pl K).H1c ρ) + Module.finrank k M) ∧
      (Module.finrank k M = 0 ∨ γ σ ≠ 1 → Module.finrank k ((X.galFrame SP T Q v0 pl K).Ob ρ) =
        Module.finrank k ((X.galFrame SP T Q v0 pl K).H1c ρ)) := by
  have hlc : ∀ m, IsLocallyConstant fun g => ρ g m := fun m s =>
    (QuotientGroup.isQuotientMap_mk _).isOpen_preimage.1 (by
      have := ((nums_lc γ (Subgroup.isOpen_mono hKγ hK)).comp fun u => (u : k) • m) s
      simp only [Function.comp_def, ← hγ] at this
      exact this)
  obtain ⟨c1, -, c3⟩ := X.galCount ⟨P.loc.lf, P.loc.lt, P.loc.le, P.gf, P.ge, P.pt⟩ Ω l v0 hG k M
    ρ hlc (fun q _ g _ hg => LinearMap.ext fun m => by
      rw [hγ, show γ g = 1 from hKγ hg]; simp) σ hσ
  obtain ⟨s1, s2, s3⟩ := X.scalDim (ρ.comp (toGS Ω SP)) γ (X.cycK Ω l k) hγ
  rw [s3 hd, add_zero] at c3
  exact ⟨c1, fun e => c3.trans (congrArg _ (s1 σ e)), fun e => c3.trans (congrArg _ (s2 σ e))⟩

private theorem nums_zero {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M]
    [Module.Finite k M] (F : Frame Γ) (ρ : Representation k Γ M) (h : Module.finrank k M = 0) :
    Module.finrank k (F.H1c ρ) = 0 := by
  haveI : Subsingleton M := Module.finrank_zero_iff.1 h
  exact Module.finrank_zero_of_subsingleton

private theorem nums_all (P : CohomologyHyp) {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}
    (hG : X.GalData l SP T Q pl K) (hN : K.Normal) (hK : IsOpen (K : Set (G ℚ Ω))) {k : Type} [Field k] [Finite k]
    [CharP k l] {M : Type}
    [AddCommGroup M] [Module k M] [Module.Finite k M] (ρ : Representation k (GS Ω SP) M) (γ : G ℚ Ω →* kˣ)
    (hγ : ∀ g m, ρ (toGS Ω SP g) m = (γ g : k) • m) (hKγ : K ≤ γ.ker) {σ : G ℚ Ω} (hσ : IsCC σ)
    (k1 : X.cycK Ω l k σ = -1) (j : ℤ × ℤ) (hdim : Module.finrank k M = dimP j) (hcc : γ σ = (-1) ^ j.1)
    (sg : ℕ → G ℚ Ω) (hsg : ∀ v ∈ T, sg v ∈ Dec (F := ℚ) (pl v)) (e1 : X.cycK Ω l k (sg l) = 1)
    (hodd : j ∈ oddRoots → X.Van T pl K γ ∧ ∀ v ∈ T, γ (sg v) ≠ 1)
    (F : Frame (GS Ω SP)) (hF : F = X.galFrame SP T Q v0 pl K) :
    Module.Finite k (F.Ob ρ) ∧
    Module.finrank k (F.Ob ρ) = Module.finrank k (F.H1c ρ) + (if j = 0 then 2 else if j = wPs ∨ j = -wPs then 1 else 0) ∧
    (j ≠ 0 → j ≠ wPs → j ≠ -wPs → Module.finrank k (F.H1c ρ) = 0) := by
  subst hF
  have h2 : (-1 : kˣ) ≠ 1 := fun e => by
    have e' : ((2 : ℕ) : k) = 0 := by
      have := congrArg Units.val e
      simp only [Units.val_neg, Units.val_one] at this
      push_cast
      linear_combination -this
    exact hG.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff _ l 2).1 e'))
  have key := nums_gen P v0 hG hK ρ γ hγ hKγ hσ
  by_cases hj : j = 0 ∨ j = wPs ∨ j = -wPs
  · have e : γ σ = 1 := by
      rw [hcc]
      rcases hj with rfl | rfl | rfl <;> simp [wPs]
    obtain ⟨a1, a2, -⟩ := key (Or.inr ⟨σ, by rw [e, k1]; exact h2.symm⟩)
    refine ⟨a1, ?_, fun n1 n2 n3 => by tauto⟩
    rw [a2 e, hdim]
    congr 1
    rcases hj with rfl | rfl | rfl <;> decide
  rw [if_neg fun e => hj (Or.inl e), if_neg fun e => hj (Or.inr e), add_zero]
  by_cases ho : j ∈ oddRoots
  · obtain ⟨o1, hne⟩ := hodd ho
    have o2 : ∀ j ∈ oddRoots, j.1 = 1 ∨ j.1 = -1 := by decide
    have e : γ σ ≠ 1 := by
      rw [hcc]
      rcases o2 j ho with o | o <;> rw [o] <;> simpa using h2
    obtain ⟨a1, -, a2⟩ := key (Or.inr ⟨sg l, e1 ▸ hne l hG.l_mem⟩)
    refine ⟨a1, a2 (Or.inr e), fun _ _ _ => ?_⟩
    rw [X.h1cZero Ω l v0 hG hN _ _ ρ γ hγ hKγ (fun v hv => ⟨sg v, hsg v hv, hne v hv⟩) o1, finrank_bot]
  · have e : j ∉ wts := by
      simp only [wts, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [dimP, if_neg fun e => hj (Or.inl e), if_neg e] at hdim
    obtain ⟨a1, -, a2⟩ := key (Or.inl hdim)
    exact ⟨a1, a2 (Or.inl hdim), fun _ _ _ => nums_zero _ _ hdim⟩

theorem UpperTheory.V.GradeZeroInterpolatingElement.nums :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → CohomologyHyp → D.Nums := by
  intro Ω _ _ _ l hl c D hD P
  obtain ⟨-, f2, -, -, -, -, -, ⟨fc, -⟩, -, -, -, fo, -⟩ := facts D hD
  obtain ⟨hN, hI, hK⟩ := X.spKer D
  haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    obtain ⟨-, -, -, -, -, h0, -, hval, -⟩ := dvrFacts l c.O
    rw [hval, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff] at h0
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact h0)
  haveI : Finite (ResidueField c.O) := (abelian₂.dvr_finite l c.O).2.1
  have hTS : D.T ⊆ D.S := Finset.insert_subset hD.l_mem (by
    classical
    exact Finset.filter_subset _ _)
  have hU : ∀ p, (p ∈ D.T ∨ p ∈ D.S \ D.T) ↔ p ∈ D.S := fun p => by
    rw [← Finset.mem_union, Finset.union_sdiff_of_subset hTS]
  have hG : X.GalData l D.SP D.T (D.S \ D.T) D.pl D.rbar.ker :=
    ⟨hD.l_odd, fun p hp => hD.S_prime p ((hU p).1 hp), Finset.disjoint_sdiff, D.residueChar_mem_levelPrimes,
      fun v => exists_congr fun p => by rw [hU], fun p hp => hD.pl_over p (hD.S_prime p ((hU p).1 hp)),
      fun q _ hq => hI (hq.trans (Subgroup.relIndex_dvd_index_of_normal _ _))⟩
  obtain ⟨k1, k2⟩ := X.cycKFacts Ω l (ResidueField c.O)
  intro rb hrb h j
  let γ : G ℚ Ω →* (ResidueField c.O)ˣ := (Units.map (residue c.O).toMonoidHom).comp (D.al ^ j.1 * D.Psi ^ j.2)
  have hγ : ∀ g m, FormData.adRep h j (toGS Ω D.SP g) m = (γ g : ResidueField c.O) • m := X.spAct D rb hrb h j
  have hKγ : D.rbar.ker ≤ γ.ker := fun g hg => Units.ext (hK j g hg)
  have hdim := X.spDim c.O (ResidueField c.O) j
  have hcc : γ D.cc = (-1) ^ j.1 := by
    show Units.map (residue c.O).toMonoidHom (D.al D.cc ^ j.1 * D.Psi D.cc ^ j.2) = _
    rw [fc, hD.Psi_even, one_zpow, mul_one, map_zpow]
    congr 1
  have e1 : X.cycK Ω l (ResidueField c.O) (D.sg l) = 1 :=
    Units.ext ((k2 c (residue c.O) _).trans ((hD.om_bar _).symm.trans (f2 l D.residueChar_mem_levelPrimes).2.1))
  have hodd : j ∈ oddRoots → X.Van D.T D.pl D.rbar.ker γ ∧ ∀ v ∈ D.T, γ (D.sg v) ≠ 1 := fun ho => by
    obtain ⟨o1, -, a, b, hab, o3⟩ := nums_odd D hD ho
    refine ⟨fun z hz hc hu hT => o1 z hz hc (fun A hA g hg hk => hu A hA g hg hk) hT, fun v hv e => ?_⟩
    refine (f2 v hv).2.2 a b hab ?_
    have e' : Raw.bar (D.al ^ j.1 * D.Psi ^ j.2) (D.sg v) = 1 := congrArg Units.val e
    rw [← o3]
    show residue c.O (((D.al ^ j.1 * D.Psi ^ j.2) (D.sg v) : c.O) * (D.ps b (D.sg v) : c.O)) = _
    rw [map_mul]
    exact (congrArg (· * _) e').trans (one_mul _)
  have hF : D.frame = X.galFrame D.SP D.T (D.S \ D.T) ⟨l, D.residueChar_mem_levelPrimes⟩ D.pl D.rbar.ker := by
    unfold Raw.frame X.galFrame
    rfl
  exact nums_all P ⟨l, D.residueChar_mem_levelPrimes⟩ hG hN fo (FormData.adRep h j) γ hγ hKγ hD.isCC (k1 _ hD.isCC) j hdim hcc D.sg
    (fun v hv => (f2 v hv).1) e1 hodd D.frame hF
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpWApply
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

private theorem prj_fst {O : Type} [CommRing O] (c : Fin 4 → O) (X : M4 (DualNumber O))
    (hX : ∀ a b, (X a b).fst = Matrix.diagonal c a b) (i a b : Fin 4) :
    (prj (fun a => algebraMap O (DualNumber O) (c a)) X i a b).fst =
      if a = i ∧ b = i then ∏ j ∈ Finset.univ.erase i, (c i - c j) else 0 := by
  have hp : (∏ j ∈ Finset.univ.erase i,
      (Polynomial.X - Polynomial.C ((fun a => algebraMap O (DualNumber O) (c a)) j))) =
      (∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (c j))).map (algebraMap O (DualNumber O)) := by
    simp [Polynomial.map_prod]
  have hF : ∀ P : M4 (DualNumber O), (P a b).fst = ((TrivSqZeroExt.fstHom O O O).mapMatrix P) a b :=
    fun P => rfl
  have hXm : (TrivSqZeroExt.fstHom O O O).mapMatrix X = Matrix.diagonalAlgHom O c := by
    ext a b
    exact hX a b
  unfold prj
  rw [hp, Polynomial.aeval_map_algebraMap, hF, ← Polynomial.aeval_algHom_apply, hXm,
    Polynomial.aeval_algHom_apply, Matrix.diagonalAlgHom_apply, Matrix.diagonal_apply]
  simp only [map_prod, Finset.prod_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Pi.sub_apply,
    Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  by_cases hab : a = b
  · subst hab
    by_cases hai : a = i
    · subst hai
      simp
    · rw [if_pos rfl, if_neg (fun h => hai h.1)]
      exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hai, Finset.mem_univ _⟩) (sub_self _)
  · rw [if_neg hab, if_neg (fun h => hab (h.1.trans h.2.symm))]

private theorem triple {O : Type} [CommRing O] (A B C : M4 (DualNumber O)) (p q : Fin 4) (α γ : O) (β : Fin 4 → O)
    (hA : ∀ a b, (A a b).fst = if a = p ∧ b = p then α else 0)
    (hC : ∀ a b, (C a b).fst = if a = q ∧ b = q then γ else 0)
    (hB : ∀ a b, (B a b).fst = Matrix.diagonal β a b) :
    ((A * B * C) p q).snd = (A p q).snd * β q * γ + α * (B p q).snd * γ + α * β p * (C p q).snd := by
  simp only [Matrix.mul_apply, Fin.sum_univ_four, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul,
    TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, hA, hB, hC, Matrix.diagonal_apply, smul_eq_mul, op_smul_eq_mul]
  fin_cases p <;> fin_cases q <;> simp <;> ring

private theorem spW_apply {O : Type} [CommRing O] {w : ℤ × ℤ} {X : M4 O} (hX : X ∈ spW O w) :
    adj X = -X ∧ ∀ i j, wt i j ≠ w → X i j = 0 := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hX
  refine ⟨h1, fun i j hij => ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, Matrix.entryLinearMap_apply] at h2
  exact h2 i j hij

private theorem spW_neg {O : Type} [CommRing O] {X : M4 O} (hX : X ∈ spW O (-wPs)) : X = X 2 0 • Xm O := by
  obtain ⟨hadj, hz⟩ := spW_apply hX
  have h31 := congrFun (congrFun hadj 3) 1
  simp [adj_apply, sgn] at h31
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xm, Matrix.single_apply] <;>
    first | exact h31 | exact h31.symm | exact hz _ _ (by simp [wt, lamW, muW, wPs])

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.tanLz :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → (∀ z ∈ D.tanSet l (fun _ _ _ ρ => D.eqL ρ) (-wPs), ∃ a m : c.O, a ≠ 0 ∧ ∀ g : D.Gp l, a • z g = (((D.Psi⁻¹ g : c.Oˣ) : c.O) * m - m) • Xm c.O) ∧ ∀ z ∈ D.tanSet l (fun _ _ _ ρ => D.eqL ρ) 0, ∀ g : D.Gp l, (g : G ℚ Ω) ∈ D.Ip l → z g = 0 := by
  intro Ω _ _ _ l _ c D hG
  obtain ⟨-, -, -, -, -, hprod, hinj, -⟩ := facts D hG
  set cs : Fin 4 → c.O := fun k => ((D.ps k ↑D.s0 : c.Oˣ) : c.O) with hcs
  have hα : ∀ i, (∏ j ∈ Finset.univ.erase i, (cs i - cs j)) ≠ 0 := by
    intro i
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    rw [sub_ne_zero]
    intro h
    exact (Finset.mem_erase.1 hj).1 (hinj h).symm
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨hzw, -, ρ, ⟨-, hord⟩, hρ⟩ := hz
    have hX : ∀ a b, (ρ D.s0 a b).fst = Matrix.diagonal cs a b := fun a b => (hρ D.s0 a b).1
    have E : ∀ g : D.Gp l,
        (0 : c.O) = (prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) 2 2 0).snd *
            ((D.th g : c.Oˣ) : c.O) * (∏ j ∈ Finset.univ.erase 0, (cs 0 - cs j)) +
          (∏ j ∈ Finset.univ.erase 2, (cs 2 - cs j)) * (z g 2 0 * ((D.th g : c.Oˣ) : c.O)) *
            (∏ j ∈ Finset.univ.erase 0, (cs 0 - cs j)) +
          (∏ j ∈ Finset.univ.erase 2, (cs 2 - cs j)) * ((D.al g : c.Oˣ) : c.O) *
            (prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) 0 2 0).snd := by
      intro g
      have hs : prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) 2 * ρ g *
          prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) 0 = 0 :=
        hord.stable g 0 2 (by decide)
      have ht := triple (prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) 2) (ρ g)
        (prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) 0) 2 0 _ _
        (fun k => ((D.ps k g : c.Oˣ) : c.O)) (prj_fst cs (ρ D.s0) hX 2) (prj_fst cs (ρ D.s0) hX 0)
        (fun a b => (hρ g a b).1)
      rw [hs, (hρ g 2 0).2, show D.r0 ↑g = Matrix.diagonal fun k => ((D.ps k g : c.Oˣ) : c.O) from rfl,
        Matrix.mul_diagonal, Matrix.zero_apply, TrivSqZeroExt.snd_zero] at ht
      exact ht
    have hx1 : z 1 2 0 = 0 := by
      have h := (hρ 1 2 0).2
      simp only [map_one, OneMemClass.coe_one, mul_one, Matrix.one_apply_ne (by decide : (2 : Fin 4) ≠ 0),
        TrivSqZeroExt.snd_zero] at h
      exact h.symm
    have E1 := E 1
    simp only [map_one, OneMemClass.coe_one, Units.val_one, hx1] at E1
    refine ⟨(∏ j ∈ Finset.univ.erase 2, (cs 2 - cs j)) * (∏ j ∈ Finset.univ.erase 0, (cs 0 - cs j)),
      -((∏ j ∈ Finset.univ.erase 2, (cs 2 - cs j)) *
        (prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) 0 2 0).snd),
      mul_ne_zero (hα 2) (hα 0), fun g => ?_⟩
    rw [spW_neg (hzw g), smul_smul]
    congr 1
    have huv : ((D.Psi g : c.Oˣ) : c.O) * ((D.Psi⁻¹ g : c.Oˣ) : c.O) = 1 := by
      rw [MonoidHom.inv_apply, Units.mul_inv]
    have hth : ((D.th g : c.Oˣ) : c.O) = ((D.Psi g : c.Oˣ) : c.O) * ((D.al g : c.Oˣ) : c.O) := by
      have h := congrArg (fun f : G ℚ Ω →* c.Oˣ => ((f g : c.Oˣ) : c.O)) (hprod 1)
      simp only [show (1 : Fin 4).rev = 2 from rfl, MonoidHom.mul_apply, Units.val_mul] at h
      exact h.symm
    apply mul_left_cancel₀ (Units.ne_zero (D.th g))
    linear_combination (-1 : c.O) * E g +
      (((D.Psi⁻¹ g : c.Oˣ) : c.O) * (∏ j ∈ Finset.univ.erase 2, (cs 2 - cs j)) *
        (prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) 0 2 0).snd) * hth +
      (((D.al g : c.Oˣ) : c.O) * (∏ j ∈ Finset.univ.erase 2, (cs 2 - cs j)) *
        (prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) 0 2 0).snd) * huv +
      ((D.th g : c.Oˣ) : c.O) * E1
  · intro z hz g hg
    obtain ⟨hzw, -, ρ, ⟨-, hord⟩, hρ⟩ := hz
    have hX : ∀ a b, (ρ D.s0 a b).fst = Matrix.diagonal cs a b := fun a b => (hρ D.s0 a b).1
    have hr0 : D.r0 ↑g = Matrix.diagonal fun k => ((D.ps k g : c.Oˣ) : c.O) := rfl
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      have hs := hord.inert g (Subgroup.mem_subgroupOf.2 hg) i
      set x := algebraMap c.O (DualNumber c.O) ((D.ps i ↑g : c.Oˣ) : c.O) with hx
      have hB : ∀ a b, ((ρ g - x • 1) a b).fst =
          Matrix.diagonal (fun k => ((D.ps k g : c.Oˣ) : c.O) - ((D.ps i g : c.Oˣ) : c.O)) a b := by
        intro a b
        rw [Matrix.sub_apply, TrivSqZeroExt.fst_sub, (hρ g a b).1, hr0, Matrix.smul_apply, Matrix.one_apply]
        simp only [Matrix.diagonal_apply, hx]
        split_ifs with h
        · simp [TrivSqZeroExt.algebraMap_eq_inl]
        · simp
      have ht := triple _ _ _ i i _ _ _ (prj_fst cs (ρ D.s0) hX i) (prj_fst cs (ρ D.s0) hX i) hB
      have hs' : prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) i * (ρ g - x • 1) *
          prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) i = 0 := hs
      rw [hs', Matrix.sub_apply, TrivSqZeroExt.snd_sub, (hρ g i i).2, hr0, Matrix.mul_diagonal,
        Matrix.smul_apply, Matrix.one_apply_eq] at ht
      simp [hx, TrivSqZeroExt.algebraMap_eq_inl] at ht
      rw [Matrix.zero_apply]
      rcases ht with (h | h) | h
      · exact absurd h (hα i)
      · exact h
      · exact absurd h (hα i)
    · rw [Matrix.zero_apply]
      exact (spW_apply (hzw g)).2 i j (by rw [Ne, wt_eq_zero]; exact hij)
end

