module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0995
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalSphericalVectorOfSatakeFamily
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter

namespace GlobalTheory.JSW.SphVec

open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.LFun

theorem map_mem_twKer {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {K : Subgroup G}
    (S : V →ₗ[ℂ] W) (hS : ∀ h v, S (ρ h v) = σ h (S v)) {v : V} (hv : v ∈ twKer ρ K 1) : S v ∈ twKer σ K 1 := by
  have h : (twKer ρ K 1).map S ≤ twKer σ K 1 := by
    rw [twKer, Submodule.map_span_le]
    rintro _ ⟨n, u, rfl⟩
    exact Submodule.subset_span ⟨n, S u, by simp [hS]⟩
  exact h ⟨v, hv, rfl⟩

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_fixed_mem (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    (hS : GlobalTheory.LGrp.IsSpherical (π.locRep w) (KGL w (n := a))) (U : Submodule ℂ π.V)
    (hU : ∀ g, ∀ v ∈ U, π.locRep w g v ∈ U) {y : π.V} (hy : y ∈ U) (hy0 : y ≠ 0) :
    ∃ x ∈ U, x ≠ 0 ∧ ∀ k ∈ KGL w (n := a), π.locRep w k x = x := by
  have hK : IsCompact ((KGL w (n := a) : Subgroup _) : Set (GL (Fin a) (w.adicCompletion E))) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2
  have hsm : IsSmooth (π.locRep w) := π.isSmooth_locRep w
  have hsU : IsSmooth (GlobalTheory.PRep.sub (π.locRep w) U hU) := fun v => by
    convert hsm v.1 using 1
    ext g
    exact Subtype.ext_iff
  by_contra hne
  have hbot : fixed (GlobalTheory.PRep.sub (π.locRep w) U hU) (KGL w (n := a)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra h0
    exact hne ⟨v.1, v.2, fun h => h0 (Subtype.ext h), fun k hk =>
      congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hv k hk)⟩
  have htop := (GlobalTheory.LocGL.isCompl_fixed_twKer hsU hK).sup_eq_top
  rw [hbot, bot_sup_eq] at htop
  have hall : ∀ g, π.locRep w g y ∈ twKer (π.locRep w) (KGL w (n := a)) 1 := fun g =>
    map_mem_twKer (ρ := GlobalTheory.PRep.sub (π.locRep w) U hU) U.subtype (fun _ _ => rfl)
      (v := ⟨_, hU g y hy⟩) (htop ▸ Submodule.mem_top)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hS
  let Wl : Submodule ℂ π.V := ⨅ g, (twKer (π.locRep w) (KGL w (n := a)) 1).comap (π.locRep w g)
  have memWl : ∀ v, v ∈ Wl ↔ ∀ g, π.locRep w g v ∈ twKer (π.locRep w) (KGL w (n := a)) 1 := fun v => by
    simp [Wl, Submodule.mem_iInf]
  have stab : GlobalTheory.CuspRep.IsStable (Wl.map π.V.subtype) := by
    rintro o _ ⟨v, hv, rfl⟩
    obtain ⟨g, S, hS, ho⟩ := GlobalTheory.LocFactor.op_eq_locRep_comp π w o
    have hv' := (memWl v).1 hv
    refine ⟨π.op o v, (memWl _).2 fun h => ?_, rfl⟩
    rw [ho, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul]
    have e := LinearMap.congr_fun (hS (h * g)) v
    simp only [LinearMap.comp_apply] at e
    rw [← e]
    exact map_mem_twKer S (fun h v => LinearMap.congr_fun (hS h) v) (hv' (h * g))
  rcases π.irred _ (Submodule.map_subtype_le _ _) stab with h | h
  · have h1 : (y : Sm E a) ∈ Wl.map π.V.subtype := ⟨y, (memWl y).2 hall, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    exact hy0 (Subtype.ext h1)
  · have h1 : (x : Sm E a) ∈ Wl.map π.V.subtype := by rw [h]; exact x.2
    obtain ⟨x', hx', e⟩ := h1
    obtain rfl : x' = x := Subtype.ext e
    have h2 := (memWl x').1 hx' 1
    rw [map_one, Module.End.one_apply] at h2
    exact hx0 (Submodule.disjoint_def.1 (GlobalTheory.LocGL.isCompl_fixed_twKer hsm hK).disjoint x' hx h2)

theorem locRep_comm (π : CuspSub E a) {v w : HeightOneSpectrum (𝓞 E)} (h : w ≠ v)
    (k : GL (Fin a) (v.adicCompletion E)) (g : GL (Fin a) (w.adicCompletion E)) (x : π.V) :
    π.locRep v k (π.locRep w g x) = π.locRep w g (π.locRep v k x) := by
  simp only [CuspSub.locRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    LocSph.comm_locGL w _ (pLoc_locGL_of_ne h k)]

theorem exists_fixed_union (π : CuspSub E a) (T : Set (HeightOneSpectrum (𝓞 E))) {y : π.V} (hy0 : y ≠ 0)
    (hy : ∀ v ∈ T, ∀ k ∈ KGL v (n := a), π.locRep v k y = y) (F : Finset (HeightOneSpectrum (𝓞 E)))
    (hF : ∀ w ∈ F, GlobalTheory.LGrp.IsSpherical (π.locRep w) (KGL w (n := a))) :
    ∃ x : π.V, x ≠ 0 ∧ ∀ v, v ∈ T ∨ v ∈ F → ∀ k ∈ KGL v (n := a), π.locRep v k x = x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨y, hy0, fun v hv => hy v (by simpa using hv)⟩
  | insert w F _ ih =>
    obtain ⟨x, hx0, hx⟩ := ih fun v hv => hF v (Finset.mem_insert_of_mem hv)
    let U : Submodule ℂ π.V := ⨅ v : {v // (v ∈ T ∨ v ∈ F) ∧ w ≠ v}, fixed (π.locRep v.1) (KGL v.1 (n := a))
    have memU : ∀ z, z ∈ U ↔ ∀ v, (v ∈ T ∨ v ∈ F) → w ≠ v → ∀ k ∈ KGL v (n := a), π.locRep v k z = z := fun z => by
      simp only [U, Submodule.mem_iInf, GlobalTheory.LGrp.mem_fixed, Subtype.forall]
      exact ⟨fun h v h1 h2 => h v ⟨h1, h2⟩, fun h v h1 => h v h1.1 h1.2⟩
    obtain ⟨z, hz, hz0, hzw⟩ := exists_fixed_mem π w (hF w (Finset.mem_insert_self _ _)) U
      (fun g z hz => (memU _).2 fun v hv hne k hk => by
        rw [locRep_comm π hne, (memU z).1 hz v hv hne k hk])
      ((memU x).2 fun v hv _ => hx v hv) hx0
    refine ⟨z, hz0, fun v hv => ?_⟩
    by_cases hne : w = v
    · subst hne; exact hzw
    · refine (memU z).1 hz v (hv.imp_right fun h => ?_) hne
      exact (Finset.mem_insert.1 h).resolve_left fun e => hne e.symm

theorem exists_sphVec_of_isSpherical (π : CuspSub E a) (S : Set (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∉ S, GlobalTheory.LGrp.IsSpherical (π.locRep w) (KGL w (n := a))) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ := by
  classical
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have hev := LocSph.eventually_mem ((π.cusp φ hφ).1.level.mem_nhds (by simp))
  rw [Filter.eventually_cofinite] at hev
  obtain ⟨x, hx0, hx⟩ := exists_fixed_union π
    {w | ∀ g : GL (Fin a) (w.adicCompletionIntegers E),
      locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) ∈ {k | finRep E a k φ = φ}}
    (y := ⟨φ, hφ⟩) (fun h => h0 (congrArg Subtype.val h))
    (by rintro v hv _ ⟨g, rfl⟩; exact Subtype.ext (hv g))
    (hev.toFinset.filter (· ∉ S)) (fun w hw => hS w (Finset.mem_filter.1 hw).2)
  refine ⟨x.1, x.2, fun h => hx0 (Subtype.ext h), fun w hw k hk => congrArg Subtype.val (hx w ?_ k hk)⟩
  refine (em _).imp_right fun h => Finset.mem_filter.2 ⟨hev.mem_toFinset.2 h, hw⟩

theorem exists_sphVec (π : CuspSub E a) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∉ S, ∃ B, HasSatGL w (π.locRep w) B) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ :=
  exists_sphVec_of_isSpherical π S fun w hw => (hS w hw).elim fun _ h => h.1

theorem exists_sphVec_of_hasSat (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ)
    (h : ∀ w ∉ S, HasSatGL w (π.locRep w) (B w)) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ :=
  exists_sphVec π S fun w hw => ⟨B w, h w hw⟩

end GlobalTheory.JSW.SphVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfOrthonormalBasis
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

noncomputable section

namespace GlobalTheory.KapLat.ModelOfBasis

variable {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K)

theorem herm_sum_left (x z : B.A) {ι : Type} (s : Finset ι) (f : ι → B.A) :
    B.herm x (∑ k ∈ s, f k) z = ∑ k ∈ s, B.herm x (f k) z := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, Finset.sum_mul, map_sum]

theorem herm_sum_right (x y : B.A) {ι : Type} (s : Finset ι) (f : ι → B.A) :
    B.herm x y (∑ k ∈ s, f k) = ∑ k ∈ s, B.herm x y (f k) := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum, map_sum]

theorem herm_eq_sum {n : ℕ} (x : B.A) (b : Module.Basis (Fin n) K.E B.A)
    (hb : ∀ i j, B.herm x (b i) (b j) = if i = j then 1 else 0) (y z : B.A) :
    B.herm x y z = ∑ k, b.repr y k * K.c (b.repr z k) := by
  conv_lhs => rw [← b.sum_repr y, ← b.sum_repr z]
  rw [herm_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [herm_sum_right, Finset.sum_eq_single k]
  · rw [GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, hb, if_pos rfl]; ring
  · intro l _ hl
    rw [GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, hb, if_neg (Ne.symm hl)]; ring
  · intro h; exact absurd (Finset.mem_univ k) h

end GlobalTheory.KapLat.ModelOfBasis

open GlobalTheory.KapLat.ModelOfBasis in
theorem GlobalTheory.KapLat.exists_model_of_orthonormal_basis :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e →
    ∀ (n : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), u * B.σ u = 1 →
    ∀ b : Module.Basis (Fin n) K.E B.A, (∀ i j, B.herm x (b i) (b j) = if i = j then 1 else 0) →
    ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  intro E _ _ _ w hw K e hbr n B u x hu b hb
  let ψ : B.A ≃+ (Fin n → w.adicCompletion E) :=
    b.equivFun.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => e.toAddEquiv)
  have hψ : ∀ y k, ψ y k = e (b.repr y k) := fun y k => rfl
  have hstd : ∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z) := by
    intro y z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [herm_eq_sum B x b hb, map_sum]
    unfold stdH
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hψ, hψ, map_mul, hbr.1]
  let M : Matrix (Fin n) (Fin n) (w.adicCompletion E) := Matrix.of fun k i => e (b.repr (u * b i) k)
  have hM : ∀ y, ψ (u * y) = M *ᵥ ψ y := by
    intro y
    funext k
    have hy : u * y = ∑ i, b.repr y i • (u * b i) := by
      conv_lhs => rw [← b.sum_repr y]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hψ, hy, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_sum]
    simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, hψ, map_smul, Finsupp.smul_apply, smul_eq_mul,
      map_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hunit : cT (cj w) M * M = 1 := by
    ext i j
    have h := hstd (u * b j) (u * b i)
    rw [← GlobalTheory.UnitLemma.Basic.herm_norm, hu, mul_one, hb] at h
    simp only [stdH, hψ] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, M, Matrix.of_apply]
    rw [Finset.sum_congr rfl fun k _ => mul_comm _ _, h]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]
  have hunit' : M * cT (cj w) M = 1 := mul_eq_one_comm.mp hunit
  let γ : GLw n w := ⟨M, cT (cj w) M, hunit', hunit⟩
  refine ⟨γ, ?_, ψ, ?_, hM, hstd⟩
  · unfold UL
    rw [if_neg hw]
    show cT (cj w) M * 1 * M = 1
    rw [Matrix.mul_one, hunit]
  · intro c y
    funext k
    rw [hψ, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply, hψ, smul_eq_mul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHighestVectorRealWeightUnitaryCompact
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_kHighest_real_of_finiteDimensional : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), KRel ε E → KUnit ε E → ∀ N : Submodule ℂ V, FiniteDimensional ℂ N → KStab ε E N → N ≠ ⊥ → ∃ (μ : Fin n → ℝ) (w : V), w ∈ N ∧ w ≠ 0 ∧ KHighest ε E μ w := by
  intro n ε V _ _ E hR hU N hfd hS hN
  classical
  haveI : FiniteDimensional ℂ N := hfd
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 hN
  have hcomm : ∀ k i j, ε i = ε j → E k k * E i j - E i j * E k k =
      ((if k = i then (1 : ℂ) else 0) - (if j = k then 1 else 0)) • E i j := by
    intro k i j h
    rw [hR k k i j rfl h]
    by_cases h1 : k = i <;> by_cases h2 : j = k
    · subst h1; subst h2; simp
    · subst h1; simp [h2]
    · subst h2; simp [h1]
    · simp [h1, h2]
  let H : Module.End ℂ V := ∑ k : Fin n, ((k : ℕ) : ℂ) • E k k
  have hH : ∀ i j, ε i = ε j → H * E i j = E i j * H + (((i : ℕ) : ℂ) - (j : ℕ)) • E i j := by
    intro i j hij
    rw [← sub_eq_iff_eq_add', Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, hcomm _ _ _ hij, smul_smul, ← Finset.sum_smul]
    simp [mul_sub]
  have hHN : ∀ v ∈ N, H v ∈ N := by
    intro v hv
    simp only [H, LinearMap.sum_apply, LinearMap.smul_apply]
    exact N.sum_mem fun k _ => N.smul_mem _ (hS k k rfl v hv)
  let HN : Module.End ℂ N := H.restrict hHN
  let D : Fin n → Module.End ℂ N := fun k => (E k k).restrict (fun v hv => hS k k rfl v hv)
  obtain ⟨l, hl, hmin⟩ := Set.exists_min_image {c | HN.HasEigenvalue c} Complex.re
    (Module.End.finite_hasEigenvalue HN) (Module.End.exists_eigenvalue HN)
  have hDc : ∀ i j, D i * D j = D j * D i := by
    intro i j
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h := LinearMap.congr_fun (hcomm i j j rfl) (x : V)
    have h' : ((if i = j then (1 : ℂ) else 0) - (if j = i then 1 else 0)) = 0 := by
      by_cases h1 : i = j
      · subst h1; simp
      · simp [h1, Ne.symm h1]
    rw [h', zero_smul, LinearMap.zero_apply, LinearMap.sub_apply, sub_eq_zero] at h
    simpa [D, LinearMap.restrict_apply] using h
  obtain ⟨v, hv, hv0, ν, hν⟩ := GlobalTheory.AlgInfChar.exists_joint_eigenvector D hDc (HN.eigenspace l) hl
    (fun k u hu => by
      rw [Module.End.mem_eigenspace_iff] at hu ⊢
      apply Subtype.ext
      have h1 := LinearMap.congr_fun (hH k k rfl) (u : V)
      have h2 : H (u : V) = l • (u : V) := congrArg Subtype.val hu
      simp only [sub_self, zero_smul, add_zero, Module.End.mul_apply] at h1
      simp only [HN, D, LinearMap.restrict_apply, SetLike.val_smul]
      rw [h1, h2, map_smul])
  rw [Module.End.mem_eigenspace_iff] at hv
  have hHv : H (v : V) = l • (v : V) := congrArg Subtype.val hv
  have hEv : ∀ a, E a a (v : V) = ν a • (v : V) := fun a => congrArg Subtype.val (hν a)
  have hv0' : (v : V) ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hreal : ∀ a, (((ν a).re : ℝ) : ℂ) = ν a := by
    intro a
    have h := hU a a rfl (v : V) (v : V)
    rw [hEv, inner_smul_left, inner_smul_right] at h
    have hne : ⟪(v : V), (v : V)⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv0'
    exact Complex.conj_eq_iff_re.1 (mul_right_cancel₀ hne h)
  refine ⟨fun a => (ν a).re, v, v.2, hv0', fun a => by rw [hEv, hreal], fun a b hab he => ?_⟩
  by_contra h0
  let u : N := ⟨E a b v, hS a b he v v.2⟩
  have hu0 : u ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have hHu : HN u = (l + (((a : ℕ) : ℂ) - (b : ℕ))) • u := by
    apply Subtype.ext
    have h1 := LinearMap.congr_fun (hH a b he) (v : V)
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at h1
    simp only [HN, u, LinearMap.restrict_apply, SetLike.val_smul]
    rw [h1, hHv, map_smul, add_smul]
  have h2 := hmin _ (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hHu, hu0⟩)
  have hab' : (a : ℕ) < b := hab
  simp at h2
  exact absurd hab' (not_lt.2 (by exact_mod_cast h2))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntOfDenLe
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.FinFix

variable {p : ℕ} [Fact p.Prime]

theorem exists_int_of_den_le (D k : ℕ) (hD : 0 < D) (q : ℚ)
    (h1 : ∀ ℓ : ℕ, ℓ ≠ p → q.den.factorization ℓ ≤ D.factorization ℓ) (h2 : q.den.factorization p ≤ k) :
    ∃ m : ℤ, ((D * p ^ k : ℕ) : ℚ) * q = m := by
  have hp : p.Prime := Fact.out
  have hN : 0 < D * p ^ k := Nat.mul_pos hD (pow_pos hp.pos k)
  have hdvd : q.den ∣ D * p ^ k := by
    rw [← Nat.factorization_le_iff_dvd q.den_nz hN.ne']
    intro ℓ
    rw [Nat.factorization_mul hD.ne' (pow_ne_zero _ hp.ne_zero), Nat.factorization_pow, hp.factorization]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases hl : ℓ = p
    · subst hl; simp only [Finsupp.single_eq_same, mul_one]; have := h2; omega
    · have := h1 ℓ hl; omega
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨c * q.num, ?_⟩
  rw [hc]
  calc ((q.den * c : ℕ) : ℚ) * q = (c : ℚ) * (q * q.den) := by push_cast; ring
    _ = _ := by rw [Rat.mul_den_eq_num]; push_cast; ring

theorem grp_val_injective (G : HTGroup p) (β : G.Cˣ) :
    Function.Injective (fun y : grp G β => (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) := by
  intro y y' hyy
  have hu : (y : G.Cˣ × ℚˣ).1 = (y' : G.Cˣ × ℚˣ).1 := Units.ext hyy
  have h1 : (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * β := y.2.1
  have h2 : (((y' : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y' : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C (((y' : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * β := y'.2.1
  rw [hu] at h1
  have h3 : algebraMap ℚ G.C (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) = algebraMap ℚ G.C (((y' : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := by
    have := h1.symm.trans h2
    simpa using congrArg (· * ((β⁻¹ : G.Cˣ) : G.C)) this
  have h4 : (y : G.Cˣ × ℚˣ).2 = (y' : G.Cˣ × ℚˣ).2 := Units.ext ((algebraMap ℚ G.C).injective h3)
  exact Subtype.ext (Prod.ext hu h4)

theorem finite_fix_core (G : HTGroup p) (hG : G.a = 1) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f)
    (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) (hf' : IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f')
    (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (hsym : sh G β = β)
    (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) (h : G.GAf × Gr G 1) (z : Fin G.n → ℂ)
    (hz : 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re) :
    Set.Finite {y : grp G β | FixL G v β y z ∧
      f (h.1⁻¹ * toAfF G β x t hx y * h.1) * f' (h.2⁻¹ * toP1 G β y * h.2) ≠ 0} := by
  obtain ⟨D, hD, hAf⟩ := GlobalTheory.T.formGroup_testFunction_support_bounded_denominators p G β x t hx L f hf h.1
  obtain ⟨k, hP⟩ := GlobalTheory.T.p_adic_denominator_bound p G β K' f' hf' h.2
  obtain ⟨K, hK⟩ := GlobalTheory.T.fixed_vector_squared_bound p G hG v hv β hsym hR z hz
  set N : ℕ := D * p ^ k with hN
  have hNpos : (0 : ℝ) < N := by
    rw [hN]; exact_mod_cast Nat.mul_pos hD (pow_pos (Fact.out : p.Prime).pos k)
  set b := Module.finBasis ℚ G.C with hb
  set S : Finset G.C := Finset.univ.image (fun i => ((N : ℚ)⁻¹) • b i) with hS
  let Φ : G.C →+ (InfinitePlace G.F → Fin G.n → Fin G.n → ℂ) :=
    AddMonoidHom.mk' (fun c w i l => G.psi w c i l) (by intro a c; funext w i l; simp [map_add (f := _)])
  refine Set.Finite.of_finite_image ?_ ((grp_val_injective G β).injOn)
  refine GlobalTheory.T.finite_of_bounded_image_in_finitely_generated_subgroup Φ (fun k e he => GlobalTheory.T.embeddings_real_independent p G k e he) S _ ?_ (Real.sqrt (max K 0 * N)) ?_
  · rintro _ ⟨y, ⟨-, hne⟩, rfl⟩
    have hf1 := left_ne_zero_of_mul hne
    have hf2 := right_ne_zero_of_mul hne
    show (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∈ AddSubgroup.closure (S : Set G.C)
    rw [← b.sum_repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    obtain ⟨m, hm⟩ := exists_int_of_den_le D k hD (b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i)
      (fun ℓ hℓ => (hAf y hf1 ℓ hℓ).1 i) ((hP y hf2).1 i)
    have hN0 : (N : ℚ) ≠ 0 := by
      rw [hN]; exact_mod_cast (Nat.mul_pos hD (pow_pos (Fact.out : p.Prime).pos k)).ne'
    have e : b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i • b i = m • ((N : ℚ)⁻¹ • b i) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, ← hm, mul_comm, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
    rw [e]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by
      simp only [hS, Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact ⟨i, rfl⟩)) m
  · rintro _ ⟨y, ⟨hfix, hne⟩, rfl⟩
    have hf1 := left_ne_zero_of_mul hne
    have hf2 := right_ne_zero_of_mul hne
    have hs : (0 : ℚ) < (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := y.2.2
    obtain ⟨m, hm⟩ := exists_int_of_den_le D k hD ((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)
      (fun ℓ hℓ => (hAf y hf1 ℓ hℓ).2) (hP y hf2).2
    have hsN : ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) ≤ N := by
      have hm' : ((N : ℚ)) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹ = m := by
        rw [← hm, Units.val_inv_eq_inv_val]
      have hmpos : (0 : ℚ) < m := by
        rw [← hm']; exact mul_pos (by exact_mod_cast hNpos) (inv_pos.2 hs)
      have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast (show (0 : ℤ) < m by exact_mod_cast hmpos)
      have : (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) ≤ N := by
        have h2 : (1 : ℚ) ≤ (N : ℚ) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹ := hm' ▸ hm1
        calc (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) = 1 * (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := (one_mul _).symm
          _ ≤ ((N : ℚ) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹) * (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) :=
            mul_le_mul_of_nonneg_right h2 hs.le
          _ = N := by field_simp
      exact_mod_cast this
    have hsR : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by exact_mod_cast hs
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun w => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
    have h1 := hK y hfix w i j
    have h2 : ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i j‖ ^ 2 ≤ max K 0 * N :=
      h1.trans ((mul_le_mul_of_nonneg_right (le_max_left K 0) hsR.le).trans
        (mul_le_mul_of_nonneg_left hsN (le_max_right K 0)))
    have h3 := Real.abs_le_sqrt h2
    rwa [abs_of_nonneg (norm_nonneg _)] at h3

end GlobalTheory.FinFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsHaveSameZeroSchemeOfLineBundleIso
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem exists_sameDiv_of_lbIso : ∀ (X : Scheme.{0}) (L M : LB X) (σ : L.Sec), L.IsLB → M.IsLB → LBIso L M →
    ∃ τ : M.Sec, SameDiv σ τ := by
  intro X L M σ hL hM h
  obtain ⟨u, hu⟩ := LBIso.symm h
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.secOfIso (u := u) σ hu hM hL, fun x => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ x))
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x))
  refine ⟨M.U j ⊓ L.U i, i, j, inf_le_right, inf_le_left,
    ReciprocityTheory.ChartRestriction.G.Semi.res (ReciprocityTheory.ChartRestriction.G.DVR.divLe j i) (u.s (i, j)), ⟨hj, hi⟩, ?_⟩
  have e := ReciprocityTheory.ChartRestriction.G.DVR.secOfIso_spec (u := u) σ hu hM hL j i
  unfold ReciprocityTheory.ChartRestriction.G.DVR.isoCand at e
  change _ = _ * (ReciprocityTheory.ChartRestriction.G.DVR.rs (inf_le_left : M.U j ⊓ L.U i ≤ M.U j)
    ((ReciprocityTheory.ChartRestriction.G.DVR.secOfIso (u := u) σ hu hM hL).f j))
  rw [e, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

end GlobalTheory.LogPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentFrameFormsBaseChangeStatement
section
open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_frameForms_baseChange : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N mu) (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu), Function.Injective b → F.Ok → (∀ (n : ℕ) (x : Fin n → NablaT F.O N mu), LinearIndependent F.O x → LinearIndependent (PadicAlgCl l) fun a => b (x a)) → ∀ (n : ℕ) (x : Fin n → Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu)), LinearIndependent F.O x → LinearIndependent (PadicAlgCl l) fun a => (fun g => b ((x a : F.G → NablaT F.O N mu) g)) := by
  first | exact @GlobalTheory.BaseChangeIndep.forms_indep | exact GlobalTheory.BaseChangeIndep.forms_indep | (intros; apply GlobalTheory.BaseChangeIndep.forms_indep <;> assumption)
end

