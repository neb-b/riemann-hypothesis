module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.CharDom
section
noncomputable section

open ValuativeRel
open scoped Classical

namespace UpperTheory.Gal.Join

private theorem indep {T : Type} [CommGroup T] (M : Submonoid T) (hM : ∀ t : T, ∃ s ∈ M, s * t ∈ M) (t₀ : T)
    (E E' : Multiset (T →* ℂˣ)) (c c' : ℂ) (hc : c ≠ 0)
    (h : ∀ t ∈ M, c * (E.map fun μ => (μ (t₀ * t) : ℂ)).sum = c' * (E'.map fun μ => (μ (t₀ * t) : ℂ)).sum) :
    ∀ μ ∈ E, μ ∈ E' := by
  classical
  let ρ : (T →* ℂˣ) → (M →* ℂ) := fun μ => (Units.coeHom ℂ).comp (μ.comp M.subtype)
  have hρm : ∀ μ (m : M), ρ μ m = (μ m : ℂ) := fun _ _ => rfl
  have hρinj : Function.Injective ρ := by
    intro μ ν hμν
    have hM' : ∀ m ∈ M, μ m = ν m := by
      intro m hm
      apply Units.ext
      have := DFunLike.congr_fun hμν ⟨m, hm⟩
      rw [hρm, hρm] at this
      exact this
    refine MonoidHom.ext fun t => ?_
    obtain ⟨s, hs, hst⟩ := hM t
    have e : t = s⁻¹ * (s * t) := by rw [inv_mul_cancel_left]
    rw [e, map_mul μ, map_mul ν, map_inv μ, map_inv ν, hM' s hs, hM' _ hst]
  have hli : LinearIndependent ℂ (fun μ : T →* ℂˣ => ((ρ μ : M →* ℂ) : M → ℂ)) :=
    (linearIndependent_monoidHom M ℂ).comp ρ hρinj
  intro μ hμ
  by_contra hμ'
  let S := (E + E').toFinset
  let g : (T →* ℂˣ) → ℂ := fun ν => (c * E.count ν - c' * E'.count ν) * (ν t₀ : ℂ)
  have conv : ∀ F : Multiset (T →* ℂˣ), F.toFinset ⊆ S → ∀ t : T,
      (F.map fun ν => (ν (t₀ * t) : ℂ)).sum = ∑ ν ∈ S, (F.count ν : ℂ) * ((ν t₀ : ℂ) * (ν t : ℂ)) := by
    intro F hF t
    rw [Finset.sum_multiset_map_count, Finset.sum_subset hF]
    · apply Finset.sum_congr rfl
      intro ν _
      rw [nsmul_eq_mul, map_mul, Units.val_mul]
    · intro ν _ hν
      rw [Multiset.count_eq_zero.mpr (by simpa using hν)]
      simp
  have hsum : ∑ ν ∈ S, g ν • ((ρ ν : M →* ℂ) : M → ℂ) = 0 := by
    funext m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have h1 := h m m.2
    rw [conv E (fun x hx => Multiset.mem_toFinset.mpr
        (Multiset.mem_add.mpr (Or.inl (Multiset.mem_toFinset.mp hx)))) m,
      conv E' (fun x hx => Multiset.mem_toFinset.mpr
        (Multiset.mem_add.mpr (Or.inr (Multiset.mem_toFinset.mp hx)))) m,
      Finset.mul_sum, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
    rw [← h1]
    apply Finset.sum_congr rfl
    intro ν _
    rw [hρm]
    simp only [g]
    ring
  have h0 := linearIndependent_iff'.mp hli S g hsum μ
    (Multiset.mem_toFinset.mpr (Multiset.mem_add.mpr (Or.inl hμ)))
  simp only [g, Multiset.count_eq_zero.mpr hμ', Nat.cast_zero, mul_zero, sub_zero] at h0
  rcases mul_eq_zero.mp h0 with h2 | h2
  · rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hc h3
    · exact (Multiset.count_pos.mpr hμ).ne' (by exact_mod_cast h3)
  · exact (μ t₀).ne_zero h2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private def domM (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    Submonoid (Fin n → kˣ) where
  carrier := {t | Dom t}
  mul_mem' := by
    intro a b ha hb i j hij
    simp only [Pi.mul_apply, Units.val_mul, map_mul]
    exact mul_le_mul' (ha i j hij) (hb i j hij)
  one_mem' := by
    intro i j _
    simp

private theorem dom_translate (t : Fin n → kˣ) : ∃ s ∈ domM k n, s * t ∈ domM k n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, (domM k 0).one_mem, ?_⟩
    show Dom _
    intro i
    exact i.elim0
  · obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
      (fun p => valuation k ((t p.1 / t p.2 : kˣ) : k)) ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
    have hx1 : 1 ≤ valuation k ((t p.1 / t p.2 : kˣ) : k) := by
      have := hp (⟨0, hn⟩, ⟨0, hn⟩) (Finset.mem_univ _)
      simpa using this
    have hxt : ∀ i j, valuation k (t i : k) ≤
        valuation k ((t p.1 / t p.2 : kˣ) : k) * valuation k (t j : k) := by
      intro i j
      have := hp (i, j) (Finset.mem_univ _)
      have e : (t i : k) = ((t i / t j : kˣ) : k) * (t j : k) := by simp
      rw [e, map_mul]
      gcongr
    refine ⟨fun i => (t p.1 / t p.2) ^ (i : ℕ), ?_, ?_⟩
    · show Dom _
      intro i j hij
      simp only [Units.val_pow_eq_pow_val, map_pow]
      exact pow_le_pow_right₀ hx1 (le_of_lt hij)
    · show Dom _
      intro i j hij
      simp only [Pi.mul_apply, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
      have hij' : (i : ℕ) + 1 ≤ j := hij
      have hpw := pow_le_pow_right₀ hx1 hij'
      calc valuation k ((t p.1 / t p.2 : kˣ) : k) ^ (i : ℕ) * valuation k (t i : k)
          ≤ valuation k ((t p.1 / t p.2 : kˣ) : k) ^ (i : ℕ) *
            (valuation k ((t p.1 / t p.2 : kˣ) : k) * valuation k (t j : k)) := by
            gcongr
            exact hxt i j
        _ = valuation k ((t p.1 / t p.2 : kˣ) : k) ^ ((i : ℕ) + 1) * valuation k (t j : k) := by
            rw [pow_succ, mul_assoc]
        _ ≤ valuation k ((t p.1 / t p.2 : kˣ) : k) ^ (j : ℕ) * valuation k (t j : k) := by
            gcongr

theorem charDom : CharDom := by
  intro k _ _ _ _ n t₀ E E' c c' hc h
  have hind := indep (domM k n) (fun t => dom_translate t) t₀ E E' c c' hc h
  refine ⟨hind, fun hE => ?_⟩
  by_contra hne
  push_neg at hne
  obtain ⟨μ, hμ⟩ := Multiset.exists_mem_of_ne_zero hE
  have := indep (domM k n) (fun t => dom_translate t) t₀ E 0 1 0 one_ne_zero
    (fun t ht => by rw [one_mul, hne t ht]; simp) μ hμ
  simp at this

end UpperTheory.Gal.Join
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.DcosOp
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.dcosOp :
    UpperTheory.Gal.Join.DcosOp := by
  intro G V _ _ _ _ _ _ μ _ _ _ _ π hπ K hK e he x
  have hfx : ∀ {v : V}, v ∈ fixed π K ↔ ∀ k ∈ K, π k v = v := GlobalTheory.IwahoriInj.mem_fixed
  set D : Set G := {g | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} with hDdef
  have hDc : IsCompact D := by
    convert (hK.1.prod hK.1).image (f := fun y : G × G => y.1 * x * y.2) (by fun_prop) using 1
    ext g
    exact ⟨fun ⟨a, ha, b, hb, h⟩ => ⟨(a, b), ⟨ha, hb⟩, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y.1, hy.1, y.2, hy.2, h.symm⟩⟩
  have hDm : MeasurableSet D := hDc.measurableSet
  have hL : ∀ k ∈ K, ∀ g, k * g ∈ D ↔ g ∈ D := by
    have h1 : ∀ k ∈ K, ∀ g, g ∈ D → k * g ∈ D := by
      rintro k hk _ ⟨a, ha, b, hb, rfl⟩
      exact ⟨k * a, mul_mem hk ha, b, hb, by simp only [mul_assoc]⟩
    refine fun k hk g => ⟨fun h => ?_, h1 k hk g⟩
    simpa using h1 _ (inv_mem hk) _ h
  have hR : ∀ k ∈ K, ∀ g, g * k ∈ D ↔ g ∈ D := by
    have h1 : ∀ k ∈ K, ∀ g, g ∈ D → g * k ∈ D := by
      rintro k hk _ ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b * k, mul_mem hb hk, by simp only [mul_assoc]⟩
    refine fun k hk g => ⟨fun h => ?_, h1 k hk g⟩
    simpa using h1 _ (inv_mem hk) _ h
  obtain ⟨A, hA⟩ := GlobalTheory.IwahoriTraceProof.exists_setOp μ hπ hDc hDm
  have hsep : ∀ y z : V, (∀ l : Module.Dual ℂ V, l y = l z) → y = z := fun y z h => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, h l, sub_self]
  have hAr : ∀ k ∈ K, ∀ v, A (π k v) = A v := fun k hk v => hsep _ _ fun l => by
    rw [(hA _ l).2, (hA v l).2, ← integral_indicator hDm, ← integral_indicator hDm,
      ← integral_mul_right_eq_self (D.indicator fun g => l (π g v)) k]
    congr 1
    funext g
    by_cases h : g ∈ D
    · simp [h, (hR k hk g).2 h]
    · have h' : g * k ∉ D := fun h' => h ((hR k hk g).1 h')
      simp [h, h']
  have hAl : ∀ k ∈ K, ∀ v, π k (A v) = A v := fun k hk v => hsep _ _ fun l => by
    have h0 := (hA v (l ∘ₗ π k)).2
    rw [LinearMap.comp_apply] at h0
    rw [h0, (hA v l).2, ← integral_indicator hDm, ← integral_indicator hDm,
      ← integral_mul_left_eq_self (D.indicator fun g => l (π g v)) k]
    congr 1
    funext g
    by_cases h : g ∈ D
    · simp [h, (hL k hk g).2 h]
    · have h' : k * g ∉ D := fun h' => h ((hL k hk g).1 h')
      simp [h, h']
  have hAe : ∀ v, A (e v) = A v := fun v => he.lin V A v fun k hk => hAr k hk v
  have heA : ∀ v, e (A v) = A v := fun v => he.fix _ (hfx.2 fun k hk => hAl k hk v)
  have hval : ∀ v, A v = (μ.real D : ℂ) • e (π x (e v)) := fun v => hsep _ _ fun l => by
    have hw : ∀ k ∈ K, π k (e v) = e v := hfx.1 (he.mem v)
    have h0 := (hA (e v) (l ∘ₗ e)).2
    rw [LinearMap.comp_apply, heA, hAe] at h0
    rw [h0, map_smul, smul_eq_mul,
      setIntegral_congr_fun (g := fun _ => l (e (π x (e v)))) hDm fun g hg => ?_]
    · simp [Measure.real]
    · obtain ⟨a, ha, b, hb, rfl⟩ := hg
      simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply, hw b hb, he.inv a ha]
  intro v l
  have hind : (fun g => D.indicator (fun _ => (1 : ℂ)) g * l (π g v)) = D.indicator fun g => l (π g v) := by
    funext g
    by_cases h : g ∈ D <;> simp [h]
  rw [hind]
  refine ⟨(integrable_indicator_iff hDm).2 (hA v l).1, ?_⟩
  rw [integral_indicator hDm, ← (hA v l).2, hval v]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.DcosVol
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

namespace UpperTheory.Gal.Join

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem mem_dcos_iff {K : Subgroup (GL (Fin n) k)} (hK : IwLev K) {t : Fin n → kˣ} (ht : Dom t)
    (g : GL (Fin n) k) :
    g ∈ dcos K t ↔ ∃ u ∈ unipB k (Fin n), u ∈ K ∧ ∃ i ∈ K, g = u * diagT k (Fin n) t * i := by
  refine ⟨?_, fun ⟨u, _, hu, i, hi, e⟩ => ⟨u, hu, i, hi, e⟩⟩
  rintro ⟨a, ha, b, hb, rfl⟩
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := hK.fact a ha
  refine ⟨u, hu.2, hu.1, _, mul_mem (mul_mem hd (hK.low t ht c hc)) hb, ?_⟩
  have e : diagT k (Fin n) t * diagT k (Fin n) d = diagT k (Fin n) d * diagT k (Fin n) t := by
    rw [← map_mul, mul_comm, map_mul]
  calc u * diagT k (Fin n) d * c * diagT k (Fin n) t * b
      = u * (diagT k (Fin n) d * diagT k (Fin n) t) * ((diagT k (Fin n) t)⁻¹ * c * diagT k (Fin n) t) * b := by
        group
    _ = _ := by rw [← e]; group

private theorem dcos_eq_image (K : Subgroup (GL (Fin n) k)) (t : Fin n → kˣ) :
    dcos K t = (fun x : GL (Fin n) k × GL (Fin n) k => x.1 * diagT k (Fin n) t * x.2) ''
      ((K : Set (GL (Fin n) k)) ×ˢ (K : Set (GL (Fin n) k))) := by
  ext g
  exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨(a, b), ⟨ha, hb⟩, e.symm⟩, fun ⟨x, hx, e⟩ => ⟨x.1, hx.1, x.2, hx.2, e.symm⟩⟩

private theorem isCompact_dcos {K : Subgroup (GL (Fin n) k)} (hK : CO K) (t : Fin n → kˣ) :
    IsCompact (dcos K t) := by
  rw [dcos_eq_image]
  exact (hK.1.prod hK.1).image (by fun_prop)

private theorem isOpen_dcos {K : Subgroup (GL (Fin n) k)} (hK : CO K) (t : Fin n → kˣ) :
    IsOpen (dcos K t) := by
  have e : dcos K t = ⋃ a ∈ (K : Set (GL (Fin n) k)),
      (fun g => (a * diagT k (Fin n) t) * g) '' (K : Set (GL (Fin n) k)) := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop]
    exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, e.symm⟩, fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, e.symm⟩⟩
  rw [e]
  exact isOpen_biUnion fun a _ => (Homeomorph.mulLeft (a * diagT k (Fin n) t)).isOpenMap _ hK.2

open GlobalTheory.SplitWeil GlobalTheory.IwahoriTraceProof in
private theorem isClosed_unipB : IsClosed (unipB k (Fin n) : Set (GL (Fin n) k)) := by
  have e : (unipB k (Fin n) : Set (GL (Fin n) k)) = (⋂ i, ⋂ j, ⋂ _ : j < i, {g : GL (Fin n) k | g.val i j = 0}) ∩
      ⋂ i, {g : GL (Fin n) k | g.val i i = 1} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    exact mem_unipB k
  rw [e]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const).inter
    (isClosed_iInter fun i => isClosed_eq (Units.continuous_val.matrix_elem i i) continuous_const)


open GlobalTheory.SplitWeil GlobalTheory.IwahoriTraceProof in
private theorem measure_dcos [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : Measure (GL (Fin n) k))
    [μ.IsHaarMeasure] {K : Subgroup (GL (Fin n) k)} (hK : IwLev K) {t : Fin n → kˣ} (ht : Dom t) :
    μ.real (dcos K t) = μ.real (K : Set (GL (Fin n) k)) * (deltaB t)⁻¹ := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  letI : MeasurableSpace (unipRad k (points (Fin n))) := _root_.borel _
  haveI : BorelSpace (unipRad k (points (Fin n))) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unipRad k (points (Fin n))) :=
    (UnipHaar.unipHomeo (points (Fin n))).isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (unipRad k (points (Fin n))) :=
    (UnipHaar.unipHomeo (points (Fin n))).secondCountableTopology
  let ν : Measure (unipRad k (points (Fin n))) := Measure.haar
  have ho : IsOpen {s : unipRad k (points (Fin n)) | (s : GL (Fin n) k) ∈ K} :=
    hK.co.2.preimage continuous_subtype_val
  have hcl : IsClosed (unipRad k (points (Fin n)) : Set (GL (Fin n) k)) := isClosed_unipB
  have hc : IsCompact {s : unipRad k (points (Fin n)) | (s : GL (Fin n) k) ∈ K} :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK.co.1
  have h1 := measure_mul_eq μ ν hK.co.2 (t := diagT k (Fin n) t)
    (fun u hu => by simpa [unipB] using conj_mem_unipB t⁻¹ hu)
    (fun u hu hI => hK.up t ht u ⟨hI, hu⟩)
    (isCompact_dcos hK.co t).measurableSet (mem_dcos_iff hK ht)
  have h2 := UnipHaar.haar_conj_eq_modulus_mul k (Fin n) (Fin n) (fun _ => Unit) (points (Fin n)) ν
    (leviTorus k (Fin n) t) _ ho.measurableSet
  rw [← deltaB_eq_modulus] at h2
  have h3 := (congrArg (· * μ (dcos K t)) h2).symm.trans h1
  rw [mul_right_comm, ENNReal.mul_left_inj (ho.measure_pos ν ⟨1, one_mem K⟩).ne' hc.measure_lt_top.ne] at h3
  rw [measureReal_def, measureReal_def, ← h3, ENNReal.toReal_mul, ENNReal.toReal_ofReal (deltaB_pos t).le,
    mul_right_comm, mul_inv_cancel₀ (deltaB_pos t).ne', one_mul]

end

end UpperTheory.Gal.Join

theorem UpperTheory.Gal.Join.dcosVol :
    UpperTheory.Gal.Join.DcosVol := by
  intro k _ _ _ _ n _ _ μ _ K hK t ht
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc := isCompact_dcos hK.co t
  refine ⟨⟨(LocallyConstant.indicator (1 : LocallyConstant (GL (Fin n) k) ℂ) ⟨hc.isClosed, isOpen_dcos hK.co t⟩).2,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩, measure_dcos μ hK ht⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ExistsCommonEigenvector
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private lemma exists_common_eigenvector {ι M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (f : ι → Module.End ℂ M) (hc : ∀ i j, f i * f j = f j * f i) (W : Submodule ℂ M) (hW : W ≠ ⊥)
    (hst : ∀ i, ∀ y ∈ W, f i y ∈ W) :
    ∃ y ∈ W, y ≠ 0 ∧ ∀ i, ∃ c : ℂ, f i y = c • y :=
  _root_.UpperTheory.Reformulated.B.CommonEigenvectorInInvariantComplexSubspace.exists_common_eigenvector f hc W hW hst

theorem UpperTheory.Gal.Join.twExp :
    UpperTheory.Gal.Join.TwExp := by
  intro T X _ _ _ ρ P _ s A hρ hA hAρ t₁ htr
  let r : T → Module.End ℂ P := fun t => (ρ t).restrict (hρ t)
  let A' : Module.End ℂ P := A.restrict hA
  have r_apply : ∀ t (y : P), ((r t y : P) : X) = ρ t y := fun t y => rfl
  have A_apply : ∀ y : P, ((A' y : P) : X) = A y := fun y => rfl
  have r_mul : ∀ a b, r (a * b) = r a * r b := by
    intro a b
    ext y
    simp [r_apply, Module.End.mul_apply, map_mul]
  have hcomm : ∀ a b, r a * r b = r b * r a := by
    intro a b
    rw [← r_mul, ← r_mul, mul_comm]
  have hsemi : ∀ t, A' * r t = r (s t) * A' := by
    intro t
    ext y
    simp [r_apply, A_apply, Module.End.mul_apply, hAρ]
  let N : (T → ℂ) → Submodule ℂ P := fun χ => ⨅ t, (r t).maxGenEigenspace (χ t)
  have hmaps : ∀ a b c, Set.MapsTo (r a) ((r b).maxGenEigenspace c) ((r b).maxGenEigenspace c) :=
    fun a b c => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm b a) c
  have hind : iSupIndep N := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo r hmaps
  have htop : ⨆ χ, N χ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute r
      (fun a b _ => hcomm a b) (fun t => Module.End.iSup_maxGenEigenspace_eq_top (r t))
  let f : Module.End ℂ P := r t₁ * A'
  have hAN : ∀ χ, Set.MapsTo f (N χ) (N (χ ∘ s.symm)) := by
    intro χ y hy
    have hy' : ∀ t, y ∈ (r t).maxGenEigenspace (χ t) := fun t => (Submodule.mem_iInf _).mp hy t
    refine (Submodule.mem_iInf _).mpr fun t => ?_
    have key : A' y ∈ (r t).maxGenEigenspace (χ (s.symm t)) := by
      obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp (hy' (s.symm t))
      refine (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨k, ?_⟩
      have hsb : SemiconjBy A' (r (s.symm t) - χ (s.symm t) • (1 : Module.End ℂ P))
          (r t - χ (s.symm t) • (1 : Module.End ℂ P)) := by
        have h1 := hsemi (s.symm t)
        rw [MulEquiv.apply_symm_apply] at h1
        unfold SemiconjBy
        rw [mul_sub, sub_mul, h1]
        simp
      have := congrArg (fun g : Module.End ℂ P => g y) (hsb.pow_right k).eq
      simp only [Module.End.mul_apply, hk, map_zero] at this
      exact this.symm
    exact hmaps t₁ t _ key

  have hex : ∃ χ : T → ℂ, χ ∘ s = χ ∧ N χ ≠ ⊥ := by
    by_contra hno
    push_neg at hno
    let J := {χ : T → ℂ // χ ∘ s ≠ χ}
    let N' : J → Submodule ℂ P := fun j => N j.1
    have hind' : iSupIndep N' := hind.comp Subtype.val_injective
    have htop' : ⨆ j, N' j = ⊤ := by
      rw [eq_top_iff, ← htop]
      refine iSup_le fun χ => ?_
      by_cases h : χ ∘ s = χ
      · rw [hno χ h]
        exact bot_le
      · exact le_iSup N' ⟨χ, h⟩
    have hint : DirectSum.IsInternal N' :=
      DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind' htop'
    have hne : ∀ χ : T → ℂ, χ ∘ s ≠ χ → χ ∘ s.symm ≠ χ := by
      intro χ h e
      apply h
      funext t
      have := congrFun e (s t)
      simpa using this.symm
    let σ : J → J := fun j => ⟨j.1 ∘ s.symm, by
      intro e
      apply hne j.1 j.2
      funext t
      have := congrFun e t
      simpa [Function.comp] using this.symm⟩
    have hσ : ∀ j, σ j ≠ j := fun j e => hne j.1 j.2 (congrArg Subtype.val e)
    have hzero : LinearMap.trace ℂ P f = 0 :=
      LinearMap.trace_eq_zero_of_mapsTo_ne hint σ hσ (fun j => hAN j.1)
    apply htr
    have hst : ∀ y ∈ P, (ρ t₁ ∘ₗ A) y ∈ P := fun y hy => hρ t₁ _ (hA y hy)
    have hfeq : (ρ t₁ ∘ₗ A).restrict hst = f := by
      ext y
      rfl
    unfold trIn
    rw [dite_eq_left hst, hfeq, hzero]
  obtain ⟨χ, hχ, hN⟩ := hex
  have hNst : ∀ t, ∀ y ∈ N χ, r t y ∈ N χ := by
    intro t y hy
    exact (Submodule.mem_iInf _).mpr fun t' => hmaps t t' _ ((Submodule.mem_iInf _).mp hy t')
  obtain ⟨y, hyN, hy0, hy⟩ := exists_common_eigenvector r hcomm (N χ) hN hNst
  choose c hc using hy
  have hcχ : ∀ t, c t = χ t := by
    intro t
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp ((Submodule.mem_iInf _).mp hyN t)
    have hpow : ∀ m : ℕ, ((r t - χ t • (1 : Module.End ℂ P)) ^ m) y = (c t - χ t) ^ m • y := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, hc t]
        simp only [LinearMap.smul_apply, Module.End.one_apply, ← sub_smul, smul_smul, pow_succ']
        ring_nf
    rw [hpow k] at hk
    have := (smul_eq_zero.mp hk).resolve_right hy0
    by_contra hne
    exact pow_ne_zero k (sub_ne_zero.mpr hne) this
  have hc1 : c 1 = 1 := by
    have h1 : r 1 = 1 := by
      ext v
      simp [r_apply]
    have h2 := hc 1
    rw [h1, Module.End.one_apply] at h2
    have h3 : (c 1 - 1) • y = 0 := by
      rw [sub_smul, one_smul, ← h2, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hy0)
  have hcmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    have h2 := hc (a * b)
    rw [r_mul, Module.End.mul_apply, hc b, map_smul, hc a, smul_smul] at h2
    have h3 : (c (a * b) - c b * c a) • y = 0 := by
      rw [sub_smul, ← h2, sub_self]
    rw [sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hy0), mul_comm]
  let m : T →* ℂ := { toFun := c, map_one' := hc1, map_mul' := hcmul }
  refine ⟨m.toHomUnits, fun t => ?_, (y : X), y.2, fun h => hy0 (Subtype.ext h), fun t => ?_⟩
  · apply Units.ext
    simp only [MonoidHom.coe_toHomUnits]
    change c (s t) = c t
    rw [hcχ, hcχ]
    exact congrFun hχ t
  · simp only [MonoidHom.coe_toHomUnits]
    change ρ t (y : X) = c t • (y : X)
    exact congrArg Subtype.val (hc t)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.QuotEmb
section
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

theorem UpperTheory.Gal.Join.quotEmb :
    UpperTheory.Gal.Join.QuotEmb := by
  intro k _ _ _ _ n V _ _ π hπ hirr ω l hl0 hl
  exact GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hirr (torusChar ω) l hl0 hl
end

